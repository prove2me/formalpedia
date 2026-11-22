-- Prove2me | Definitions.Def_Arm64_Syscalls_Fs_Select
-- name    : Arm64_Syscalls_Fs_Select
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:08:00.440999+00:00
-- url     : https://prove2.me/theorems/bb08f52f-063c-4b2c-836d-0088cd70a128
-- title:
--   Arm64.Trusted.Syscalls.Fs.Select — Standard-Descriptor ppoll Probe
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Fs/Select.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/Select.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Fs/Select.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Fs/Select.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Fs/Select.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Standard-Descriptor `ppoll` Probe

Models the Linux AArch64 `ppoll` syscall (`__NR_ppoll = 73`, `fs/select.c:1109`,
`include/uapi/asm-generic/poll.h:28`) restricted to non-blocking descriptor-validity probes
on `fd ∈ {0, 1, 2}` with `events = 0`, zero timeout, and null signal mask. Any call outside
this subset fails closed.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `ppoll` syscall number (`__NR_ppoll = 73`,
    `include/uapi/asm-generic/unistd.h:220`, `fs/select.c:1109`). -/
def SYS_PPOLL : BitVec 64 := 73#64

/-- `struct pollfd.revents` bit reporting an invalid / closed file descriptor
    (`POLLNVAL = 0x0020`, `include/uapi/asm-generic/poll.h:19`). -/
def POLLNVAL : BitVec 16 := 0x0020#16

/-- Evaluate `rem` 8-byte `struct pollfd` entries (`{ int fd; short events; short revents; }`,
    `include/uapi/asm-generic/poll.h:28`) starting at index `idx` from `ufds` for non-blocking
    standard-descriptor validity probes (`fd ∈ {0, 1, 2}`, `events = 0`):
    - in Linux `do_pollfd` (`fs/select.c:882`), if `fdget(fd)` finds no open file (`fs.fds fd = none`),
      `revents` receives `POLLNVAL` (`0x0020`) and the ready count increments by `1`;
    - if `fd` is an open `.stdio` or `.localFile` descriptor, `vfs_poll` masked with
      `events | EPOLLERR | EPOLLHUP` (`events = 0`, no error/hangup on regular files or modeled
      standard streams) yields `revents = 0` and leaves the ready count unchanged;
    - `[INTENTIONAL_SCOPE]`: any entry outside `fd ∈ {0, 1, 2}`, with `events ≠ 0`, or backed by
      `.custom _` returns `none` so `execPpoll` fails closed. -/
def evalPpollEntries (fs : FsState) (m : Memory) (ufds : BitVec 64) :
    Nat → Nat → Nat → Option (Memory × Nat)
  | 0, _, count => some (m, count)
  | rem + 1, idx, count =>
    let entry := ufds + BitVec.ofNat 64 (idx * 8)
    let fd := m.read32 entry
    let events := m.read16 (entry + 4#64)
    if (fd != 0#32 && fd != 1#32 && fd != 2#32) || events != 0#16 then
      none
    else
      match fs.fds (fd.zeroExtend 64) with
      | none =>
        evalPpollEntries fs (m.write16 (entry + 6#64) POLLNVAL) ufds rem (idx + 1) (count + 1)
      | some desc =>
        if desc.kind == .stdio || desc.kind == .localFile then
          evalPpollEntries fs (m.write16 (entry + 6#64) 0#16) ufds rem (idx + 1) count
        else
          none

/-- True when every 2-byte `revents` slot (`ufds + i * 8 + 6`, `0 ≤ i < nfds`) is writable in `m`
    (`unsafe_put_user(revents, &ufds[i].revents)` in `fs/select.c:1058`). -/
def allPpollReventsWritable (m : Memory) (ufds : BitVec 64) (nfds : Nat) : Bool :=
  (List.range nfds).all fun i => m.canWrite (ufds + BitVec.ofNat 64 (i * 8 + 6)) 2

/-- True when at least one `revents` byte (`ufds + i * 8 + 6`, `0 ≤ i < nfds`) is writable in `m`
    (used to fail closed when `do_sys_poll` would write a prefix of `revents` before faulting). -/
def anyPpollReventsWritable (m : Memory) (ufds : BitVec 64) (nfds : Nat) : Bool :=
  (List.range nfds).any fun i => m.canWrite (ufds + BitVec.ofNat 64 (i * 8 + 6)) 1

/-- `ppoll(ufds, nfds, tsp, sigmask, sigsetsize)` (`__NR_ppoll = 73`, `SYSCALL_DEFINE5(ppoll)` in
    `fs/select.c:1109` and `set_user_sigmask` in `kernel/signal.c:3158`), restricted to non-blocking
    descriptor-validity probes on `fd ∈ {0, 1, 2}` with `events = 0`, zero timeout, and null
    signal mask:
    - `tsp` (`X2`):
      - `tsp == 0` (infinite timeout) fails closed with `.Exception "unmodeled ppoll (null timeout)"` (`[INTENTIONAL_SCOPE]`);
      - unreadable 16-byte `struct __kernel_timespec` at `tsp` returns `-EFAULT` (`get_timespec64`);
      - negative `tv_sec`, negative `tv_nsec`, or `tv_nsec ≥ 1_000_000_000` returns `-EINVAL`
        (`poll_select_set_timeout` / `timespec64_valid` in `include/linux/time64.h`);
      - any valid non-zero timeout (`tv_sec ≠ 0` or `tv_nsec ≠ 0`) fails closed with
        `.Exception "unmodeled ppoll (non-zero timeout)"`;
    - `sigmask` (`X3`) and `sigsetsize` (`X4`):
      - when `sigmask == 0`, `set_user_sigmask` (`kernel/signal.c:3158`) returns `0` immediately without
        inspecting `sigsetsize`;
      - when `sigmask ≠ 0` and `sigsetsize ≠ 8`, returns `-EINVAL`;
      - when `sigmask ≠ 0` and `sigsetsize == 8`, fails closed with
        `.Exception "unmodeled ppoll (non-null sigmask)"`;
    - `ufds` (`X0`) and `nfds` (`W1`, `unsigned int nfds` in `do_sys_poll`, `fs/select.c:1022`):
      - `nfds > FsState.maxOpenFds` (fixed ceiling `1024`; configurable `RLIMIT_NOFILE` is not
        modeled) returns `-EINVAL`;
      - `nfds == 0`: returns `-EFAULT` if `ufds.toNat > USER_VA_LIMIT` (`scoped_user_write_access_size`
        -> `access_ok(ufds, 0)` in `fs/select.c:1049`), and `0` otherwise;
      - if `[ufds, ufds + nfds * 8)` wraps modulo `2 ^ 64` or is not readable, returns `-EFAULT`;
      - evaluates all `nfds` entries via `evalPpollEntries` (failing closed with
        `.Exception "unmodeled ppoll"` if any entry has `fd ∉ {0, 1, 2}`, `events ≠ 0`, or a
        `.custom` backend);
      - checks writability of each 2-byte `revents` field (`ufds + i * 8 + 6`, `put_user` in
        `fs/select.c:1058`), returning `-EFAULT` when no `revents` byte is writable and failing
        closed with `.Exception` on partial-prefix `revents` faults;
      - otherwise writes `revents` (`0` for open, `POLLNVAL` for closed) and returns the count of
        entries with non-zero `revents`.
    - `[OVERPINNED_BEHAVIOR]`: Validates `tsp` (`get_timespec64`) -> `sigsetsize` (`set_user_sigmask`) ->
      `nfds` -> `ufds` readability / `revents` writability, matching `fs/select.c:1118-1135`. -/
def execPpoll (s : State) : State :=
  let ufds       := s.readReg64 Reg.x0
  let nfds       := (s.readReg32 Reg.x1).toNat
  let tsp        := s.readReg64 Reg.x2
  let sigmask    := s.readReg64 Reg.x3
  let sigsetsize := s.readReg64 Reg.x4
  if tsp == 0#64 then
    s.setStatus (.Exception "unmodeled ppoll (null timeout)")
  else if !decide (tsp.toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm (·.r) tsp 16 then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if !s.mem.canRead tsp 16 then
    s.setStatus (.Exception "ppoll timespec in lazy-free memory")
  else
    let tvSec  := s.mem.read64 tsp
    let tvNsec := s.mem.read64 (tsp + 8#64)
    if tvSec.slt 0#64 || tvNsec.slt 0#64 || !decide (tvNsec.toNat < 1000000000) then
      (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if tvSec != 0#64 || tvNsec != 0#64 then
      s.setStatus (.Exception "unmodeled ppoll (non-zero timeout)")
    else if sigmask != 0#64 && sigsetsize != 8#64 then
      (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if sigmask != 0#64 then
      s.setStatus (.Exception "unmodeled ppoll (non-null sigmask)")
    else if nfds > FsState.maxOpenFds then
      (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if nfds == 0 then
      if !decide (ufds.toNat ≤ USER_VA_LIMIT) then
        (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
      else
        (s.writeReg64 Reg.x0 0#64).advancePC
    else if !decide (ufds.toNat + nfds * 8 ≤ 2 ^ 64) || !s.mem.allPerm (·.r) ufds (nfds * 8) then
      (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if !s.mem.canRead ufds (nfds * 8) then
      s.setStatus (.Exception "ppoll ufds in lazy-free memory")
    else
      match evalPpollEntries s.fs s.mem ufds nfds 0 0 with
      | none => s.setStatus (.Exception "unmodeled ppoll")
      | some (m', count) =>
        if !allPpollReventsWritable s.mem ufds nfds then
          if !anyPpollReventsWritable s.mem ufds nfds then
            (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
          else
            s.setStatus (.Exception "unmodeled ppoll partial revents fault")
        else
          ((s.setMem m').writeReg64 Reg.x0 (BitVec.ofNat 64 count)).advancePC

end Arm64


