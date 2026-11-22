-- Prove2me | Definitions.Def_Arm64_Syscalls_Fs_Ioctl
-- name    : Arm64_Syscalls_Fs_Ioctl
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:07:22.497005+00:00
-- url     : https://prove2.me/theorems/7463c33e-77ac-425c-a2d5-0cd4bad5b4d2
-- title:
--   Arm64.Trusted.Syscalls.Fs.Ioctl — Linux VFS ioctl Syscall
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Fs/Ioctl.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/Ioctl.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Fs/Ioctl.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/Ioctl.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Fs/Ioctl.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Linux VFS `ioctl` Syscall

Models Linux AArch64 `ioctl` (`__NR_ioctl = 29`, `fs/ioctl.c` `SYSCALL_DEFINE3(ioctl)` and
`do_vfs_ioctl`), covering `FIOCLEX`, `FIONCLEX`, `FIONREAD` on regular files, and `-ENOTTY` for
terminal-only `'T'` commands on regular files.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `ioctl` syscall number (`__NR_ioctl = 29`, `include/uapi/asm-generic/unistd.h:111`, `fs/ioctl.c:583`). -/
def SYS_IOCTL : BitVec 64 := 29#64

/-- Generic VFS ioctl commands (`include/uapi/asm-generic/ioctls.h:46,53,85-87,106`): `FIONREAD`
    (`0x541B`), `FIONBIO` (`0x5421`), `FIONCLEX` (`0x5450`), `FIOCLEX` (`0x5451`), `FIOASYNC`
    (`0x5452`), and `FIOQSIZE` (`0x5460`), all handled by `do_vfs_ioctl` before `vfs_ioctl`. -/
def FIONREAD_W32 : BitVec 32 := 0x541B#32
def FIONBIO_W32  : BitVec 32 := 0x5421#32
def FIONCLEX_W32 : BitVec 32 := 0x5450#32
def FIOCLEX_W32  : BitVec 32 := 0x5451#32
def FIOASYNC_W32 : BitVec 32 := 0x5452#32
def FIOQSIZE_W32 : BitVec 32 := 0x5460#32

/-- `cmd` is a terminal (`_IOC_TYPE(cmd) == 'T'`, `include/uapi/asm-generic/ioctls.h`) command
    that `do_vfs_ioctl` (`fs/ioctl.c:492`) does not handle itself, so on a regular file it falls
    through `file_ioctl` -> `vfs_ioctl` and returns `-ENOTTY`. -/
def isTtyOnlyIoctl (cmd : BitVec 32) : Bool :=
  ((cmd >>> 8) &&& 0xFF#32) == 0x54#32 && (cmd >>> 16) == 0#32 &&
    !(cmd == FIONREAD_W32 || cmd == FIONBIO_W32 || cmd == FIONCLEX_W32 ||
      cmd == FIOCLEX_W32 || cmd == FIOASYNC_W32 || cmd == FIOQSIZE_W32)

/-- `ioctl(fd, cmd, arg)` (`__NR_ioctl = 29`, `fs/ioctl.c:583` `SYSCALL_DEFINE3(ioctl)` ->
    `do_vfs_ioctl` at `fs/ioctl.c:492`), reading the low 32 bits of `X1` as `unsigned int cmd`:
    - closed fds `≥ 3` and negative fds return `-EBADF`;
    - `FIOCLEX` / `FIONCLEX` on open `.localFile` or `.localDir` descriptors set / clear
      `FdEntry.cloexec` and return `0` (`set_close_on_exec`);
    - `FIONREAD` on `.localFile` stores the 32-bit `int` `i_size - f_pos` (truncated, as by
      `put_user(i_size_read(inode) - filp->f_pos, (int __user *)argp)`) at `arg` and returns `0`,
      or returns `-EFAULT` if `arg` is not 4-byte writable;
    - terminal-only `cmd`s (`isTtyOnlyIoctl`, e.g. `TCGETS`, `TIOCGWINSZ`) on `.localFile` return
      `-ENOTTY`, assuming the file system's `unlocked_ioctl` handles no `'T'` commands;
    - `[INTENTIONAL_SCOPE]`: other `cmd`s on `.localFile` (`FIONBIO`, `FIOASYNC`, `FIOQSIZE`,
      `FIGETBSZ`, `FS_IOC_*`, ...), unmodeled stdio fds, other `cmd`s on `.localDir`, and other
      descriptor kinds trap fail-closed. -/
def execIoctl (s : State) : State :=
  let rawFd := s.readReg32 Reg.x0
  let cmd   := s.readReg32 Reg.x1
  let arg   := s.readReg64 Reg.x2
  if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | some desc =>
      if (desc.kind == .localFile || desc.kind == .localDir) &&
          (cmd == FIOCLEX_W32 || cmd == FIONCLEX_W32) then
        let fs' := s.fs.setFd fd (some { desc with cloexec := cmd == FIOCLEX_W32 })
        ((s.setFs fs').writeReg64 Reg.x0 0#64).advancePC
      else if desc.kind != .localFile then s.setStatus (.Exception "unmodeled non-file fd")
      else if cmd == FIONREAD_W32 then
        if !decide (arg.toNat + 4 ≤ 2 ^ 64) || !s.mem.canWrite arg 4 then
          (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else
          let avail : BitVec 32 :=
            BitVec.ofNat 32 (s.fs.fdBytes desc).length - BitVec.ofNat 32 desc.offset
          ((s.setMem (s.mem.writeBytes arg (leBytes32 avail))).writeReg64 Reg.x0 0#64).advancePC
      else if isTtyOnlyIoctl cmd then (s.writeReg64 Reg.x0 (-ENOTTY)).advancePC
      else s.setStatus (.Exception "unmodeled ioctl cmd")
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC

end Arm64


