-- Prove2me | Definitions.Def_Arm64_Syscalls_Drivers_Random
-- name    : Arm64_Syscalls_Drivers_Random
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:10:18.937816+00:00
-- url     : https://prove2.me/theorems/42af8471-9bc0-4e4a-b08f-b058ce0a1f62
-- title:
--   Arm64.Trusted.Syscalls.Drivers.Random — Entropy Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Drivers/Random.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Drivers/Random.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Drivers/Random.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Drivers/Random.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Drivers/Random.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common

/-!
# Entropy Syscalls

Defines the Linux AArch64 `getrandom` syscall number (`SYS_GETRANDOM = 278`), `GRND_*` flag
constants (`include/uapi/linux/random.h`), and handler `execGetrandom` (`drivers/char/random.c`).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `getrandom` syscall number (`__NR_getrandom = 278`, `include/uapi/asm-generic/unistd.h:762`, `drivers/char/random.c:1395`). -/
def SYS_GETRANDOM : BitVec 64 := 278#64

/-- Linux `getrandom` flags (`include/uapi/linux/random.h:47-49`). -/
def GRND_NONBLOCK   : BitVec 32 := 0x0001#32
def GRND_RANDOM     : BitVec 32 := 0x0002#32
def GRND_INSECURE   : BitVec 32 := 0x0004#32
def GRND_KNOWN_MASK : BitVec 32 := GRND_NONBLOCK ||| GRND_RANDOM ||| GRND_INSECURE

/-- `getrandom(buf, count, flags)` (`__NR_getrandom = 278`, `drivers/char/random.c:1395`):
    - `flags` is `unsigned int` (`W2`): rejects bits outside `GRND_KNOWN_MASK` (`0x7`) and the
      mutually exclusive combination `GRND_INSECURE | GRND_RANDOM` (`0x6`) with `-EINVAL`.
    - Assumes an initialized kernel CRNG, so `GRND_NONBLOCK` never returns `-EAGAIN` and valid
      requests fill `count` bytes from `s.oracle.getrandom s.oracleIdx`.
    - Checks `flags` before `import_ubuf` (`lib/iov_iter.c:1445`: `access_ok(buf, min(count, MAX_RW_COUNT))`,
      so `count == 0` with `buf > USER_VA_LIMIT` returns `-EFAULT` before `get_random_bytes_user`
      returns `0`) and before checking `s.mem.canWrite buf count.toNat` (`copy_to_iter`).
    - `-EFAULT` when `count == 0` with `buf > USER_VA_LIMIT` (`import_ubuf` `access_ok`) or when
      `count > 0` and the first byte of `buf` is not writable (`get_random_bytes_user` returns
      `-EFAULT` only when nothing was copied; on loaded process states `[USER_VA_LIMIT, 2 ^ 64)` is
      unmapped, so `!s.mem.canWrite buf 1` also rejects `buf + count > 2 ^ 64`).
    - `[INTENTIONAL_SCOPE]`: Fails closed with `.Exception` when `count > MAX_RW_COUNT`
      (`0x7ffff000`; Linux `import_ubuf` clamps to a short `MAX_RW_COUNT` read) and when `buf` is
      writable for a nonempty prefix but faults later (Linux returns the short copied count). -/
def execGetrandom (s : State) : State :=
  let buf := s.readReg64 Reg.x0
  let count := s.readReg64 Reg.x1
  let flags := s.readReg32 Reg.x2
  if (flags &&& ~~~GRND_KNOWN_MASK) != 0#32 ||
      (flags &&& (GRND_RANDOM ||| GRND_INSECURE)) == (GRND_RANDOM ||| GRND_INSECURE) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if count.toNat > MAX_RW_COUNT then
    s.setStatus (.Exception "unmodeled getrandom count > MAX_RW_COUNT (short read)")
  else if count == 0#64 then
    if !decide (buf.toNat ≤ USER_VA_LIMIT) then
      (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else
      (s.writeReg64 Reg.x0 0#64).advancePC
  else if !s.mem.canWrite buf count.toNat then
    if !s.mem.canWrite buf 1 then
      (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else s.setStatus (.Exception "unmodeled getrandom partial-fault short read")
  else
    let bytes := (List.range count.toNat).map (s.oracle.getrandom s.oracleIdx)
    (((s.setMem (s.mem.writeBytes buf bytes)).nextOracle).writeReg64 Reg.x0 count).advancePC

end Arm64


