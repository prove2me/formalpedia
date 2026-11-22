-- Prove2me | Definitions.Def_Arm64_Syscalls_Kernel_Signal
-- name    : Arm64_Syscalls_Kernel_Signal
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:09:39.843376+00:00
-- url     : https://prove2.me/theorems/f9aec4c1-e06d-465c-bce7-095ba42d7878
-- title:
--   Arm64.Trusted.Syscalls.Kernel.Signal — Signal and Abort Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Kernel/Signal.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Signal.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Kernel/Signal.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Kernel/Signal.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Kernel/Signal.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Signal and Abort Syscalls

Linux 7.3 AArch64 signal syscall numbers, ABI constants, `SigAction`/`SigAltStack` binary
layouts, and execution semantics for `rt_sigprocmask` (`kernel/signal.c:3247`), `sigaltstack`
(`kernel/signal.c:4515`, `include/linux/sched/signal.h:571-608`), `rt_sigaction`
(`kernel/signal.c:4551`), `tgkill` (`kernel/signal.c:4024`), and `tkill` (`kernel/signal.c:4038`).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `tkill` syscall number (`__NR_tkill = 130`, `include/uapi/asm-generic/unistd.h:358`, `kernel/signal.c:4038`). -/
def SYS_TKILL : BitVec 64 := 130#64

/-- Linux AArch64 `tgkill` syscall number (`__NR_tgkill = 131`, `include/uapi/asm-generic/unistd.h:360`, `kernel/signal.c:4024`). -/
def SYS_TGKILL : BitVec 64 := 131#64

/-- Linux AArch64 `sigaltstack` syscall number (`__NR_sigaltstack = 132`, `include/uapi/asm-generic/unistd.h:362`, `kernel/signal.c:4515`). -/
def SYS_SIGALTSTACK : BitVec 64 := 132#64

/-- Linux AArch64 `rt_sigaction` syscall number (`__NR_rt_sigaction = 134`, `include/uapi/asm-generic/unistd.h:366`, `kernel/signal.c:4551`). -/
def SYS_RT_SIGACTION : BitVec 64 := 134#64

/-- Linux AArch64 `rt_sigprocmask` syscall number (`__NR_rt_sigprocmask = 135`, `include/uapi/asm-generic/unistd.h:368`, `kernel/signal.c:3247`). -/
def SYS_RT_SIGPROCMASK : BitVec 64 := 135#64

/-- POSIX / Linux `SIGABRT` (`SIGIOT`) signal number (`6`, `include/uapi/asm-generic/signal.h:20`). -/
def LINUX_SIGABRT : BitVec 32 := 6#32

/-- POSIX / Linux `SIGBUS` signal number (`7`, `include/uapi/asm-generic/signal.h:21`). -/
def LINUX_SIGBUS : BitVec 32 := 7#32

/-- POSIX / Linux `SIGKILL` signal number (`9`, `include/uapi/asm-generic/signal.h:23`). -/
def LINUX_SIGKILL : BitVec 32 := 9#32

/-- POSIX / Linux `SIGSEGV` signal number (`11`, `include/uapi/asm-generic/signal.h:25`). -/
def LINUX_SIGSEGV : BitVec 32 := 11#32

/-- POSIX / Linux `SIGSTOP` signal number (`19`, `include/uapi/asm-generic/signal.h:33`). -/
def LINUX_SIGSTOP : BitVec 32 := 19#32

/-- Default signal disposition constant (`SIG_DFL = 0`, `include/uapi/asm-generic/signal-defs.h:22`). -/
def SIG_DFL : BitVec 64 := 0#64

/-- Ignore signal disposition constant (`SIG_IGN = 1`, `include/uapi/asm-generic/signal-defs.h:23`). -/
def SIG_IGN : BitVec 64 := 1#64

/-- Bitmask of signals stripped from `sa_mask` and `sigMask` (`sigmask(SIGKILL) | sigmask(SIGSTOP)
    = (1 << 8) | (1 << 18) = 0x40100`, `SIG_KERNEL_ONLY_MASK` in `include/linux/signal.h:403`). -/
def SIG_UNBLOCKABLE_MASK : BitVec 64 := 0x40100#64

/-- Bitmask bit for `SIGABRT` (`sigmask(6) = 1 << 5 = 0x20`, `sigmask` in
    `include/linux/signal.h:340`, `SIGABRT = 6` in `include/uapi/asm-generic/signal.h:20`). -/
def SIGABRT_MASK : BitVec 64 := 0x20#64

/-- AArch64 `sa_flags` bits kept by `do_sigaction` (`act->sa.sa_flags &= UAPI_SA_FLAGS` in
    `kernel/signal.c:4401-4404`): `UAPI_SA_FLAGS = SA_NOCLDSTOP | SA_NOCLDWAIT | SA_SIGINFO |
    SA_ONSTACK | SA_RESTART | SA_NODEFER | SA_RESETHAND | SA_EXPOSE_TAGBITS | __ARCH_UAPI_SA_FLAGS`
    (`include/linux/signal_types.h:76-86`) with `__ARCH_UAPI_SA_FLAGS = SA_RESTORER` on arm64
    (`0x04000000`, `arch/arm64/include/uapi/asm/signal.h:21`), i.e.
    `0x1 | 0x2 | 0x4 | 0x08000000 | 0x10000000 | 0x40000000 | 0x80000000 | 0x800 | 0x04000000`
    (`include/uapi/asm-generic/signal-defs.h:30-65`), zero-extended to the 64-bit `sa_flags`. -/
def UAPI_SA_FLAGS : BitVec 64 := 0xDC000807#64

/-- Alternate signal stack active flag (`SS_ONSTACK = 1`, `include/uapi/linux/signal.h:8`). -/
def SS_ONSTACK : BitVec 32 := 1#32

/-- Alternate signal stack disabled flag (`SS_DISABLE = 2`, `include/uapi/linux/signal.h:9`). -/
def SS_DISABLE : BitVec 32 := 2#32

/-- Alternate signal stack auto-disarm flag (`SS_AUTODISARM = 1U << 31`, `include/uapi/linux/signal.h:12`). -/
def SS_AUTODISARM : BitVec 32 := 0x80000000#32

/-- Minimum AArch64 alternate signal stack byte size (`MINSIGSTKSZ = 5120`,
    `arch/arm64/include/uapi/asm/signal.h:23`; note `2048` in `asm-generic` is 32-bit compat only). -/
def MINSIGSTKSZ : Nat := 5120

/-- Serialize a 32-byte AArch64 `struct k_sigaction` (`handler`, `flags`, `restorer`, `mask`) in
    little-endian byte order (`include/linux/signal_types.h`). -/
def SigAction.toBytes (sa : SigAction) : List (BitVec 8) :=
  leBytes64 sa.handler ++ leBytes64 sa.flags ++ leBytes64 sa.restorer ++ leBytes64 sa.mask

/-- Whether the recorded raw `sas_ss_flags` word of `sas` has `SS_AUTODISARM` set
    (`current->sas_ss_flags & SS_AUTODISARM` in `include/linux/sched/signal.h:595`). -/
def SigAltStack.autodisarm (sas : SigAltStack) : Bool :=
  (sas.ssFlags &&& SS_AUTODISARM) != 0#32

/-- True when stack pointer `sp` lies on the active alternate signal stack `sas`
    (`on_sig_stack` / `__on_sig_stack` for downward-growing AArch64 stacks in
    `include/linux/sched/signal.h:571-600`): returns `false` when `sas.autodisarm` is set
    (`SS_AUTODISARM`) or `sas.size = 0`, and otherwise checks `sas.sp < sp ∧ sp - sas.sp ≤ sas.size`
    using unsigned 64-bit arithmetic (`(sas.sp, sas.sp + sas.size]`). -/
def SigAltStack.onSigStack (sas : SigAltStack) (sp : BitVec 64) : Bool :=
  !sas.autodisarm && BitVec.ult sas.sp sp && BitVec.ule (sp - sas.sp) sas.size

/-- Reported 32-bit `ss_flags` word for `sas` at stack pointer `sp`
    (`sas_ss_flags(sp) | (current->sas_ss_flags & SS_FLAG_BITS)` in
    `include/linux/sched/signal.h:602-608` and `kernel/signal.c:4468-4469`). -/
def SigAltStack.flags (sas : SigAltStack) (sp : BitVec 64) : BitVec 32 :=
  let mode :=
    if sas.size == 0#64 then SS_DISABLE
    else if sas.onSigStack sp then SS_ONSTACK
    else 0#32
  if sas.autodisarm then mode ||| SS_AUTODISARM else mode

/-- Serialize a 24-byte AArch64 `stack_t` (`ss_sp : u64` at `+0`, `ss_flags : i32` at `+8`, 4 zero
    padding bytes at `+12` from `memset(oss, 0, sizeof(stack_t))`, `ss_size : u64` at `+16`;
    `include/uapi/asm-generic/signal.h:85-89`, `kernel/signal.c:4465-4469`). -/
def SigAltStack.toBytes (sas : SigAltStack) (sp : BitVec 64) : List (BitVec 8) :=
  leBytes64 sas.sp ++ leBytes32 (sas.flags sp) ++ [0#8, 0#8, 0#8, 0#8] ++ leBytes64 sas.size

/-- `rt_sigprocmask(how, set, oldset, sigsetsize)` (`__NR_rt_sigprocmask = 135`,
    `kernel/signal.c:3247` `SYSCALL_DEFINE4(rt_sigprocmask)`):
    tracks the per-thread 64-bit blocked signal mask (`State.sigMask`) and delivers unblocked
    pending signals (`State.sigPending &&& ~~~State.sigMask`) synchronously on syscall return:
    - validates `sigsetsize == 8` (`sizeof(sigset_t)` on 64-bit Linux, `-EINVAL`), non-wrapping
      8-byte readability of `set` when non-null (`-EFAULT`, or `.Exception` on lazy-free memory),
      and `how ∈ {SIG_BLOCK(0), SIG_UNBLOCK(1), SIG_SETMASK(2)}` when `set ≠ 0` (`-EINVAL`);
    - updates `State.sigMask` according to `how`, stripping `SIG_UNBLOCKABLE_MASK` (`SIGKILL` /
      `SIGSTOP`) per `sigdelsetmask` in `set_current_blocked` (`kernel/signal.c:3204,3262`);
    - when `oldset ≠ 0`, writes `leBytes64 oldMask` to `oldset` (returning `-EFAULT` if `oldset`
      wraps modulo `2 ^ 64` or is not 8-byte writable, matching `copy_to_user` after
      `sigprocmask` in `kernel/signal.c:3278-3281`);
    - `[INTENTIONAL_SCOPE]`: on return, checks `deliverable := s2.sigPending &&& ~~~s2.sigMask`.
      When `deliverable == SIGABRT_MASK`, clears `SIGABRT_MASK` from `sigPending` and delivers
      `SIGABRT` (`.Signaled 6#7` under `SIG_DFL`, discarded under `SIG_IGN`, or fail-closed
      `.Exception` for custom handlers); any other non-zero `deliverable` fails closed with
      `.Exception`;
    - `[OVERPINNED_BEHAVIOR]`: validates `sigsetsize` -> `copy_from_user(set)` -> `how` /
      `sigprocmask` -> `copy_to_user(oldset)` -> synchronous pending-signal check, matching
      `kernel/signal.c:3254-3281`. -/
def execRtSigprocmask (s : State) : State :=
  let how        := s.readReg32 Reg.x0
  let set        := s.readReg64 Reg.x1
  let oldset     := s.readReg64 Reg.x2
  let sigsetsize := s.readReg64 Reg.x3
  if sigsetsize != 8#64 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if set != 0#64 && !decide (set.toNat + 8 ≤ 2 ^ 64) then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if set != 0#64 && !s.mem.allPerm (·.r) set 8 then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if set != 0#64 && !s.mem.canRead set 8 then
    s.setStatus (.Exception "rt_sigprocmask set in lazy-free memory")
  else if set != 0#64 && how != 0#32 && how != 1#32 && how != 2#32 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else
    let oldMask := s.sigMask
    let s1 :=
      if set == 0#64 then s
      else
        let m := s.mem.read64 set
        let newMask :=
          (if how == 0#32 then oldMask ||| m
           else if how == 1#32 then oldMask &&& ~~~m
           else m) &&& ~~~SIG_UNBLOCKABLE_MASK
        s.setSigMask newMask
    let s2 :=
      if oldset == 0#64 then
        (s1.writeReg64 Reg.x0 0#64).advancePC
      else if !decide (oldset.toNat + 8 ≤ 2 ^ 64) || !s1.mem.canWrite oldset 8 then
        (s1.writeReg64 Reg.x0 EFAULT_RET).advancePC
      else
        ((s1.setMem (s1.mem.writeBytes oldset (leBytes64 oldMask))).writeReg64 Reg.x0 0#64).advancePC
    let deliverable := s2.sigPending &&& ~~~s2.sigMask
    if deliverable == 0#64 then
      s2
    else if deliverable == SIGABRT_MASK then
      let s3 := s2.setSigPending (s2.sigPending &&& ~~~SIGABRT_MASK)
      let disp := (s3.getSigAction LINUX_SIGABRT).handler
      if disp == SIG_DFL then
        s3.setStatus (.Signaled 6#7)
      else if disp == SIG_IGN then
        s3
      else
        s3.setStatus (.Exception "unmodeled signal handler delivery")
    else
      s2.setStatus (.Exception "unmodeled pending signal delivery")

/-- `sigaltstack(uss, uoss)` (`__NR_sigaltstack = 132`, `SYSCALL_DEFINE2(sigaltstack)` and
    `do_sigaltstack` in `kernel/signal.c:4458-4527`):
    models queries and updates of the per-thread 24-byte `stack_t` alternate signal stack
    (`ss_sp : u64` at `+0`, 32-bit `ss_flags` at `+8` ignoring 4-byte caller padding at `+12`,
    `ss_size : u64` at `+16`):
    - non-null `uss` that wraps modulo `2 ^ 64` or is not 24-byte readable returns `-EFAULT`
      (`copy_from_user(&new, uss, sizeof(stack_t))` before state mutation);
    - when `uss ≠ 0` and `s.sigAltStack.onSigStack s.sp` (`sp ∈ (sas.sp, sas.sp + sas.size]`
      without `SS_AUTODISARM`), returns `-EPERM`;
    - when `uss ≠ 0` and `(ss_flags &&& ~~~SS_AUTODISARM) ∉ {0, SS_ONSTACK, SS_DISABLE}`,
      returns `-EINVAL`;
    - when `uss ≠ 0` and `(ss_flags &&& ~~~SS_AUTODISARM) == SS_DISABLE`, records
      `{ sp := 0, size := 0, ssFlags := ss_flags }` without checking `ss_size`
      (`kernel/signal.c:4496-4499`); otherwise records `{ sp := ss_sp, size := ss_size,
      ssFlags := ss_flags }` after requiring `ss_size ≥ MINSIGSTKSZ` (`5120`, returning `-ENOMEM`
      if smaller) unless the recorded `(sas_ss_sp, sas_ss_size, sas_ss_flags)` already equals
      `(ss_sp, ss_size, ss_flags)`: that unchanged-settings early return (`kernel/signal.c:4486-4493`,
      after the `-EPERM`/`-EINVAL` checks and before `SS_DISABLE` normalization and the
      `MINSIGSTKSZ` check) leaves the state unchanged, which equals the store below (every
      reachable recorded `SS_DISABLE`-mode setting already has `sp = size = 0`);
    - when `uoss ≠ 0`, writes the previous 24-byte zero-padded `stack_t` snapshot (`oldBytes`,
      captured before updating `s.sigAltStack`) to `uoss` (returning `-EFAULT` if `uoss` wraps
      modulo `2 ^ 64` or is not 24-byte writable, matching `copy_to_user(uoss, &old, sizeof(stack_t))`
      after `do_sigaltstack` in `kernel/signal.c:4521-4525`);
    - `[OVERPINNED_BEHAVIOR]`: checks `copy_from_user(uss)` -> `do_sigaltstack` ->
      `copy_to_user(uoss)`, matching `kernel/signal.c:4519-4526`. -/
def execSigaltstack (s : State) : State :=
  let uss     := s.readReg64 Reg.x0
  let uoss    := s.readReg64 Reg.x1
  let ssSp    := s.mem.read64 uss
  let ssFlags := s.mem.read32 (uss + 8#64)
  let ssSize  := s.mem.read64 (uss + 16#64)
  let ssMode  := ssFlags &&& ~~~SS_AUTODISARM
  if uss != 0#64 && (!decide (uss.toNat + 24 ≤ 2 ^ 64) || !s.mem.allPerm (·.r) uss 24) then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if uss != 0#64 && !s.mem.canRead uss 24 then
    s.setStatus (.Exception "sigaltstack uss in lazy-free memory")
  else if uss != 0#64 && s.sigAltStack.onSigStack s.sp then
    (s.writeReg64 Reg.x0 (-EPERM)).advancePC
  else if uss != 0#64 && ssMode != SS_DISABLE && ssMode != SS_ONSTACK && ssMode != 0#32 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if uss != 0#64 && ssMode != SS_DISABLE && ssSize.toNat < MINSIGSTKSZ &&
      s.sigAltStack != { sp := ssSp, size := ssSize, ssFlags } then
    (s.writeReg64 Reg.x0 (-ENOMEM)).advancePC
  else
    let oldBytes := s.sigAltStack.toBytes s.sp
    let s1 :=
      if uss == 0#64 then s
      else if ssMode == SS_DISABLE then
        s.setSigAltStack { sp := 0#64, size := 0#64, ssFlags }
      else
        s.setSigAltStack { sp := ssSp, size := ssSize, ssFlags }
    if uoss == 0#64 then
      (s1.writeReg64 Reg.x0 0#64).advancePC
    else if !decide (uoss.toNat + 24 ≤ 2 ^ 64) || !s1.mem.canWrite uoss 24 then
      (s1.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else
      ((s1.setMem (s1.mem.writeBytes uoss oldBytes)).writeReg64 Reg.x0 0#64).advancePC

/-- `rt_sigaction(signum, act, oldact, sigsetsize)` (`__NR_rt_sigaction = 134`,
    `SYSCALL_DEFINE4(rt_sigaction)` and `do_sigaction` in `kernel/signal.c:4551`):
    models per-signal `SIG_DFL` (`0`) and `SIG_IGN` (`1`) disposition queries and updates across
    the 64 Linux signals (`1 ≤ signum ≤ 64`, `_NSIG = 64`), plus recording user-space handlers
    for the synchronous hardware fault signals `SIGBUS` (`7`) and `SIGSEGV` (`11`), in
    `State.sigActions` without asynchronous signal delivery:
    - `sigsetsize != 8` (`sizeof(sigset_t)`) returns `-EINVAL`;
    - non-null `act` that wraps modulo `2 ^ 64` or is not 32-byte readable returns `-EFAULT`
      (`copy_from_user`);
    - `signum ≤ 0` or `signum > 64` returns `-EINVAL` (`!valid_signal(sig)`);
    - non-null `act` with `signum == SIGKILL` (`9`) or `signum == SIGSTOP` (`19`) returns `-EINVAL`
      (`sig_kernel_only(sig)`);
    - `[INTENTIONAL_SCOPE]`: non-null `act` whose `sa_handler` is neither `SIG_DFL` (`0`) nor
      `SIG_IGN` (`1`) is permitted only when `signum == SIGSEGV` (`11`) or `signum == SIGBUS`
      (`7`) (recording the disposition in `State.sigActions`); all other signals fail closed with
      `.Exception "unmodeled rt_sigaction"`. Hardware faults in `Arm64/Trusted/ISA/Eval.lean`
      always raise `.Exception` directly (never `.Signaled` or invoking user handlers), and
      `execTkill` / `execTgkill` on `SIGSEGV` / `SIGBUS` or non-`SIG_DFL`/`SIG_IGN` `SIGABRT`
      likewise raise `.Exception`;
    - when `act ≠ 0`, records `{ handler, flags &&& UAPI_SA_FLAGS, restorer,
      mask &&& ~~~SIG_UNBLOCKABLE_MASK }` in `State.sigActions signum` (`sa_flags &= UAPI_SA_FLAGS`
      and `sigdelsetmask` in `do_sigaction`); recorded flags are thus already masked, so `oldact`
      matches Linux's `oact->sa.sa_flags &= UAPI_SA_FLAGS`. When setting `SIGABRT` to `SIG_IGN`,
      also clears `SIGABRT_MASK` from `State.sigPending` (`flush_sigqueue_mask` in
      `kernel/signal.c:4425-4437`);
    - when `oldact ≠ 0`, writes the previous 32-byte `k_sigaction` to `oldact` (returning `-EFAULT`
      if `oldact` wraps modulo `2 ^ 64` or is not 32-byte writable, matching `copy_to_user` after
      `do_sigaction`);
    - `[OVERPINNED_BEHAVIOR]`: checks `sigsetsize` -> `copy_from_user(act)` -> `do_sigaction(signum)` ->
      `copy_to_user(oldact)`, matching `kernel/signal.c:4559-4573`. -/
def execRtSigaction (s : State) : State :=
  let signum     := s.readReg32 Reg.x0
  let act        := s.readReg64 Reg.x1
  let oldact     := s.readReg64 Reg.x2
  let sigsetsize := s.readReg64 Reg.x3
  if sigsetsize != 8#64 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if act != 0#64 && (!decide (act.toNat + 32 ≤ 2 ^ 64) || !s.mem.allPerm (·.r) act 32) then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else if act != 0#64 && !s.mem.canRead act 32 then
    s.setStatus (.Exception "rt_sigaction act in lazy-free memory")
  else if signum.sle 0#32 || signum.toNat > 64 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if act != 0#64 && (signum == LINUX_SIGKILL || signum == LINUX_SIGSTOP) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if act != 0#64 && s.mem.read64 act != SIG_DFL && s.mem.read64 act != SIG_IGN &&
      signum != LINUX_SIGSEGV && signum != LINUX_SIGBUS then
    s.setStatus (.Exception "unmodeled rt_sigaction")
  else
    let old := s.getSigAction signum
    let s1 :=
      if act == 0#64 then s
      else
        let handler := s.mem.read64 act
        let sAct := s.setSigAction signum
          { handler  := handler
            flags    := s.mem.read64 (act + 8#64) &&& UAPI_SA_FLAGS
            restorer := s.mem.read64 (act + 16#64)
            mask     := s.mem.read64 (act + 24#64) &&& ~~~SIG_UNBLOCKABLE_MASK }
        if signum == LINUX_SIGABRT && handler == SIG_IGN then
          sAct.setSigPending (sAct.sigPending &&& ~~~SIGABRT_MASK)
        else
          sAct
    if oldact == 0#64 then
      (s1.writeReg64 Reg.x0 0#64).advancePC
    else if !decide (oldact.toNat + 32 ≤ 2 ^ 64) || !s1.mem.canWrite oldact 32 then
      (s1.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else
      ((s1.setMem (s1.mem.writeBytes oldact (SigAction.toBytes old))).writeReg64 Reg.x0 0#64).advancePC

/-- Maximum Linux PID ceiling (`PID_MAX_LIMIT = 4 * 1024 * 1024 = 0x400000`,
    `include/linux/threads.h:35`), above which `find_task_by_vpid` always returns `NULL` (`-ESRCH`). -/
def PID_MAX_LIMIT : Nat := 0x400000

/-- `tkill(tid, sig)` (`__NR_tkill = 130`, `SYSCALL_DEFINE2(tkill)` -> `do_tkill` ->
    `do_send_specific` in `kernel/signal.c:4194-4265`):
    - if `tid ≤ 0`, returns `-EINVAL` (`kernel/signal.c:4261`);
    - `do_send_specific` looks up `find_task_by_vpid(tid)` before validating `sig`
      (`kernel/signal.c:4200-4202`): returns `-ESRCH` when `tid > PID_MAX_LIMIT` (`0x400000`), and
      `[INTENTIONAL_SCOPE]` fails closed with `.Exception "unmodeled tkill"` for `2 ≤ tid ≤ PID_MAX_LIMIT`;
    - on `tid == 1` (`SIM_TID`), if `sig < 0` or `sig > 64` (`_NSIG`), returns `-EINVAL`
      (`valid_signal` in `check_kill_permission`);
    - if `tid == 1` and `sig == 0` (existence/permission probe), returns `0`;
    - `[INTENTIONAL_SCOPE]`: if `tid == 1` (`SIM_TID`) and `sig == SIGABRT` (`6`):
      - when `SIGABRT` is blocked in `State.sigMask` (`(s.sigMask &&& SIGABRT_MASK) != 0`), queues
        `SIGABRT_MASK` in `State.sigPending` and returns `0` (`sig_ignored` returns `false` while
        blocked in `kernel/signal.c:103-116`);
      - otherwise, when `SIGABRT`'s disposition is `SIG_DFL` (`0`), terminates the process with
        fatal signal status `.Signaled 6#7` (shell / `qemu-aarch64` exit code `128 + 6 = 134`);
      - when `SIGABRT`'s disposition is `SIG_IGN` (`1`), drops the ignored signal (`sig_ignored` in
        `kernel/signal.c`) and returns `0`;
      - otherwise fails closed with `.Exception "unmodeled tkill"`;
    - any other `(tid, sig)` pair fails closed with `.Exception "unmodeled tkill"`. -/
def execTkill (s : State) : State :=
  let tid := s.readReg32 Reg.x0
  let sig := s.readReg32 Reg.x1
  if tid.sle 0#32 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if tid != 1#32 then
    if tid.toNat > PID_MAX_LIMIT then
      (s.writeReg64 Reg.x0 (-ESRCH)).advancePC
    else
      s.setStatus (.Exception "unmodeled tkill")
  else if sig.slt 0#32 || sig.toNat > 64 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if sig == 0#32 then
    (s.writeReg64 Reg.x0 0#64).advancePC
  else if sig == LINUX_SIGABRT then
    if (s.sigMask &&& SIGABRT_MASK) != 0#64 then
      ((s.setSigPending (s.sigPending ||| SIGABRT_MASK)).writeReg64 Reg.x0 0#64).advancePC
    else
      let disp := (s.getSigAction LINUX_SIGABRT).handler
      if disp == SIG_DFL then
        s.setStatus (.Signaled 6#7)
      else if disp == SIG_IGN then
        (s.writeReg64 Reg.x0 0#64).advancePC
      else
        s.setStatus (.Exception "unmodeled tkill")
  else
    s.setStatus (.Exception "unmodeled tkill")

/-- `tgkill(tgid, tid, sig)` (`__NR_tgkill = 131`, `SYSCALL_DEFINE3(tgkill)` -> `do_tkill` ->
    `do_send_specific` in `kernel/signal.c:4194-4250`):
    - if `tid ≤ 0` or `tgid ≤ 0`, returns `-EINVAL` (`kernel/signal.c:4246`);
    - `do_send_specific` looks up `find_task_by_vpid(tid)` and checks `task_tgid_vnr(p) == tgid`
      before validating `sig` (`kernel/signal.c:4200-4202`): returns `-ESRCH` when `tid == 1` and
      `tgid != 1` or when `tid > PID_MAX_LIMIT`, and `[INTENTIONAL_SCOPE]` fails closed with
      `.Exception "unmodeled tgkill"` for `2 ≤ tid ≤ PID_MAX_LIMIT`;
    - on `tgid == 1` and `tid == 1` (`SIM_TID`), if `sig < 0` or `sig > 64` (`_NSIG`), returns
      `-EINVAL`;
    - if `tgid == 1`, `tid == 1`, and `sig == 0` (existence/permission probe), returns `0`;
    - `[INTENTIONAL_SCOPE]`: if `tgid == 1`, `tid == 1` (`SIM_TID`), and `sig == SIGABRT` (`6`):
      - when `SIGABRT` is blocked in `State.sigMask` (`(s.sigMask &&& SIGABRT_MASK) != 0`), queues
        `SIGABRT_MASK` in `State.sigPending` and returns `0` (`sig_ignored` returns `false` while
        blocked in `kernel/signal.c:103-116`);
      - otherwise, when `SIGABRT`'s disposition is `SIG_DFL` (`0`), terminates the process with
        fatal signal status `.Signaled 6#7` (shell / `qemu-aarch64` exit code `128 + 6 = 134`);
      - when `SIGABRT`'s disposition is `SIG_IGN` (`1`), drops the ignored signal (`sig_ignored` in
        `kernel/signal.c`) and returns `0`;
      - otherwise fails closed with `.Exception "unmodeled tgkill"`;
    - any other `(tgid, tid, sig)` triple fails closed with `.Exception "unmodeled tgkill"`. -/
def execTgkill (s : State) : State :=
  let tgid := s.readReg32 Reg.x0
  let tid  := s.readReg32 Reg.x1
  let sig  := s.readReg32 Reg.x2
  if tid.sle 0#32 || tgid.sle 0#32 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if tid != 1#32 then
    if tid.toNat > PID_MAX_LIMIT then
      (s.writeReg64 Reg.x0 (-ESRCH)).advancePC
    else
      s.setStatus (.Exception "unmodeled tgkill")
  else if tgid != 1#32 then
    (s.writeReg64 Reg.x0 (-ESRCH)).advancePC
  else if sig.slt 0#32 || sig.toNat > 64 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if sig == 0#32 then
    (s.writeReg64 Reg.x0 0#64).advancePC
  else if sig == LINUX_SIGABRT then
    if (s.sigMask &&& SIGABRT_MASK) != 0#64 then
      ((s.setSigPending (s.sigPending ||| SIGABRT_MASK)).writeReg64 Reg.x0 0#64).advancePC
    else
      let disp := (s.getSigAction LINUX_SIGABRT).handler
      if disp == SIG_DFL then
        s.setStatus (.Signaled 6#7)
      else if disp == SIG_IGN then
        (s.writeReg64 Reg.x0 0#64).advancePC
      else
        s.setStatus (.Exception "unmodeled tgkill")
  else
    s.setStatus (.Exception "unmodeled tgkill")

end Arm64


