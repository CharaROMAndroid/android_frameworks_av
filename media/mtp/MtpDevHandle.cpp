/*
 * Copyright (C) 2016 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or         implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <android-base/logging.h>
#include <cutils/properties.h>
#include <algorithm>
#include <array>
#include <cstddef>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/usb/ch9.h>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/endian.h>
#include <unistd.h>

#include "MtpDevHandle.h"
#include "mtp.h"

namespace android {

constexpr char mtp_dev_path[] = "/dev/mtp_usb";

namespace {

// Samsung's legacy MTP gadget uses a private ioctl and payload structure for
// sending files. Keep the layout identical to read_send_info in the kernel's
// drivers/usb/gadget/function/f_mtp.h.
constexpr unsigned long kSamsungWriteInterruptData = 4;
constexpr unsigned long kSamsungSetZeroLengthPacket = 9;
constexpr unsigned long kSamsungGetBulkInPacketSize = 10;
constexpr unsigned long kSamsungSendFileWithHeader = 11;

struct SamsungMtpSendInfo {
    int fd;
    alignas(8) uint64_t length;
    uint16_t command;
    uint32_t transaction_id;
};

static_assert(offsetof(SamsungMtpSendInfo, length) == 8);
static_assert(offsetof(SamsungMtpSendInfo, command) == 16);
static_assert(offsetof(SamsungMtpSendInfo, transaction_id) == 20);
static_assert(sizeof(SamsungMtpSendInfo) == 24);

struct SamsungMtpDataHeader {
    uint32_t length;
    uint16_t type;
    uint16_t command;
    uint32_t transaction_id;
};

static_assert(sizeof(SamsungMtpDataHeader) == MTP_CONTAINER_HEADER_SIZE);

int readFileFullyAt(int fd, uint8_t* data, size_t length, off_t offset) {
    size_t read = 0;
    while (read < length) {
        ssize_t count = TEMP_FAILURE_RETRY(
                ::pread(fd, data + read, length - read, offset + read));
        if (count <= 0) {
            if (count == 0) errno = EIO;
            return -1;
        }
        read += count;
    }
    return 0;
}

int writeDeviceFully(int fd, const uint8_t* data, size_t length) {
    size_t written = 0;
    while (written < length) {
        ssize_t count = TEMP_FAILURE_RETRY(::write(fd, data + written, length - written));
        if (count <= 0) {
            if (count == 0) errno = EIO;
            return -1;
        }
        written += count;
    }
    return 0;
}

int sendPartialFileWithLegacyGadget(int deviceFd, mtp_file_range mfr) {
    constexpr size_t kHeaderSize = sizeof(SamsungMtpDataHeader);
    if (mfr.length < 0 || mfr.length >
            static_cast<int64_t>(std::numeric_limits<uint32_t>::max()) -
                    static_cast<int64_t>(kHeaderSize) || mfr.offset < 0 ||
            mfr.offset > std::numeric_limits<off_t>::max() - mfr.length) {
        errno = EOPNOTSUPP;
        return -1;
    }

    int packetSize = ioctl(deviceFd, kSamsungGetBulkInPacketSize, 0);
    if (packetSize <= static_cast<int>(kHeaderSize) || packetSize > MTP_BUFFER_SIZE) {
        if (packetSize >= 0) errno = EIO;
        return -1;
    }

    const uint32_t containerLength = mfr.length + kHeaderSize;
    SamsungMtpDataHeader header = {
            .length = htole32(containerLength),
            .type = htole16(MTP_CONTAINER_TYPE_DATA),
            .command = htole16(mfr.command),
            .transaction_id = htole32(mfr.transaction_id),
    };

    std::array<uint8_t, MTP_BUFFER_SIZE> buffer;
    memcpy(buffer.data(), &header, kHeaderSize);

    // Keep the first packet header and some payload together. Some MTP hosts
    // do not handle a separate header-only bulk transfer reliably.
    size_t firstPayload = std::min<uint64_t>(
            mfr.length, packetSize - static_cast<int>(kHeaderSize));
    if (readFileFullyAt(mfr.fd, buffer.data() + kHeaderSize, firstPayload, mfr.offset) < 0 ||
            writeDeviceFully(deviceFd, buffer.data(), kHeaderSize + firstPayload) < 0) {
        return -1;
    }

    uint64_t remaining = mfr.length - firstPayload;
    off_t offset = mfr.offset + firstPayload;
    while (remaining > 0) {
        size_t chunk = std::min<uint64_t>(remaining, buffer.size());
        if (readFileFullyAt(mfr.fd, buffer.data(), chunk, offset) < 0 ||
                writeDeviceFully(deviceFd, buffer.data(), chunk) < 0) {
            return -1;
        }
        remaining -= chunk;
        offset += chunk;
    }

    if (containerLength % packetSize == 0 &&
            ioctl(deviceFd, kSamsungSetZeroLengthPacket, 0) < 0) {
        return -1;
    }
    return 0;
}

int receiveFileWithLegacyGadget(int deviceFd, mtp_file_range mfr) {
    // The Samsung kernel driver has no receive-file ioctl. Its MTP read path
    // exposes the remaining bulk OUT payload through /dev/mtp_usb, so copy a
    // known-size object in bounded chunks. The 0xFFFFFFFF length is the MTP
    // sentinel for an unknown or >=4 GiB object; this read interface cannot
    // detect its terminating short packet safely.
    if (mfr.length < 0 || mfr.length == 0xFFFFFFFFLL || mfr.offset < 0 ||
            mfr.offset > std::numeric_limits<off_t>::max() - mfr.length) {
        errno = EOPNOTSUPP;
        return -1;
    }

    std::array<uint8_t, MTP_BUFFER_SIZE> buffer;
    int64_t remaining = mfr.length;
    off_t offset = mfr.offset;
    while (remaining > 0) {
        size_t chunk = std::min<uint64_t>(remaining, buffer.size());
        ssize_t bytesRead = TEMP_FAILURE_RETRY(::read(deviceFd, buffer.data(), chunk));
        if (bytesRead <= 0) {
            if (bytesRead == 0) errno = EIO;
            return -1;
        }

        size_t written = 0;
        while (written < static_cast<size_t>(bytesRead)) {
            ssize_t bytesWritten = TEMP_FAILURE_RETRY(::pwrite(
                    mfr.fd, buffer.data() + written, bytesRead - written, offset + written));
            if (bytesWritten <= 0) {
                if (bytesWritten == 0) errno = EIO;
                return -1;
            }
            written += bytesWritten;
        }

        remaining -= bytesRead;
        offset += bytesRead;
    }
    return 0;
}

} // namespace

MtpDevHandle::MtpDevHandle()
    : mFd(-1) {};

MtpDevHandle::~MtpDevHandle() {}

int MtpDevHandle::read(void *data, size_t len) {
    return ::read(mFd, data, len);
}

int MtpDevHandle::write(const void *data, size_t len) {
    return ::write(mFd, data, len);
}

int MtpDevHandle::receiveFile(mtp_file_range mfr, bool) {
    int ret = ioctl(mFd, MTP_RECEIVE_FILE, reinterpret_cast<unsigned long>(&mfr));
    if (ret >= 0 || errno != ENOTTY) return ret;
    return receiveFileWithLegacyGadget(mFd, mfr);
}

int MtpDevHandle::sendFile(mtp_file_range mfr) {
    int ret = ioctl(mFd, MTP_SEND_FILE_WITH_HEADER, reinterpret_cast<unsigned long>(&mfr));
    if (ret >= 0 || errno != ENOTTY) return ret;

    // The Samsung legacy ioctl always starts reading at file offset zero.
    if (mfr.offset != 0) return sendPartialFileWithLegacyGadget(mFd, mfr);
    if (mfr.length < 0) {
        errno = EINVAL;
        return -1;
    }

    SamsungMtpSendInfo info{};
    info.fd = mfr.fd;
    info.length = static_cast<uint64_t>(mfr.length);
    info.command = mfr.command;
    info.transaction_id = mfr.transaction_id;
    return ioctl(mFd, kSamsungSendFileWithHeader, &info);
}

int MtpDevHandle::sendEvent(mtp_event me) {
    int ret = ioctl(mFd, MTP_SEND_EVENT, reinterpret_cast<unsigned long>(&me));
    if (ret >= 0 || errno != ENOTTY) return ret;

    // The legacy Samsung ioctl always copies a 16-byte interrupt packet.
    if (me.data == nullptr || me.length < MTP_CONTAINER_HEADER_SIZE || me.length > 16) {
        errno = EINVAL;
        return -1;
    }
    std::array<uint8_t, 16> eventData{};
    memcpy(eventData.data(), me.data, me.length);
    mtp_event samsungEvent = { .length = eventData.size(), .data = eventData.data() };
    return ioctl(mFd, kSamsungWriteInterruptData, &samsungEvent);
}

int MtpDevHandle::start(bool /* ptp */) {
    mFd.reset(TEMP_FAILURE_RETRY(open(mtp_dev_path, O_RDWR)));
    if (mFd == -1) return -1;
    return 0;
}

void MtpDevHandle::close() {
    mFd.reset();
}

} // namespace android
