-- Prove2me | Definitions.Def_Arm64_Syscalls_Include_Uapi
-- name    : Arm64_Syscalls_Include_Uapi
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:04:43.445483+00:00
-- url     : https://prove2.me/theorems/9e797d10-9f08-486c-bdd0-6c23050a795b
-- title:
--   Arm64.Trusted.Syscalls.Include.Uapi — Shared UAPI Helpers & Syscall Table Dispatcher
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Include/Uapi.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Include/Uapi.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Include/Uapi.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Include/Uapi.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Include/Uapi.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_Syscalls_Include_Errno

/-!
# Shared UAPI Helpers & Syscall Table Dispatcher (`Arm64.Trusted.Syscalls.Include.Uapi`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `arch/arm64/kernel/syscall.c:55` (`el0_svc_common`: reads `X8` syscall number, `X0..X5` args,
    writes return value to `X0`)
  - `include/uapi/asm-generic/unistd.h` (AArch64 generic syscall numbering)
- **Purpose & Key Exports**: Single-thread process/thread ID (`SIM_TID`), 48-bit user virtual
  address space ceiling (`USER_VA_LIMIT`), AArch64 top-byte-ignore pointer untagging (`untaggedAddr`),
  per-call transfer cap (`MAX_RW_COUNT`), little-endian byte encoders (`leBytes32`, `leBytes64`),
  and explicit `(nr, handler)` table dispatch (`Syscall.dispatch`).
-/

@[expose] public section

namespace Arm64

/-- Deterministic process and thread ID (`1`) returned by single-thread identity syscalls
    (`[INTENTIONAL_SCOPE]`: `kernel/sys.c:966` `sys_getpid`, `kernel/sys.c:979` `sys_gettid`). -/
def SIM_TID : BitVec 64 := 1#64

/-- Upper bound of the 48-bit Linux AArch64 user virtual address space
    (`TASK_SIZE_64 = 2 ^ 48` under `CONFIG_ARM64_VA_BITS=48` / `TCR_EL1.T0SZ = 16` with 4 KiB
    pages, `arch/arm64/include/asm/memory.h:100`, `include/asm-generic/access_ok.h:31`
    `__access_ok`; `[INTENTIONAL_SCOPE]`: assumes a `VA_BITS=48` kernel rather than 39/42/47-bit VA
    configurations where `access_ok` rejects addresses in `[2 ^ VA_BITS, 2 ^ 48)` with `-EFAULT`). -/
def USER_VA_LIMIT : Nat := 2 ^ 48

/-- Strip an AArch64 Top-Byte-Ignore (`TBI`) user-pointer tag per Linux `untagged_addr(addr)`
    (`arch/arm64/include/asm/memory.h:287-294`, `__addr &= sign_extend64(__addr, 55)`): clears
    bits `[63:56]` when bit `55` is `0` (user-half tagged pointers) and leaves `addr` unchanged
    when bit `55` is `1`. Applied unconditionally by Linux `munmap`, `mremap` (`old_address`),
    `mprotect`, and `madvise` regardless of `PR_TAGGED_ADDR_ENABLE`. -/
def untaggedAddr (addr : BitVec 64) : BitVec 64 :=
  if addr.getLsbD 55 then addr else addr &&& 0x00ffffffffffffff#64

/-- Largest byte count a single read or write transfers (`MAX_RW_COUNT = INT_MAX & PAGE_MASK =
    0x7ffff000`, `include/linux/fs.h:2447`). -/
def MAX_RW_COUNT : Nat := 0x7ffff000

/-- Serialize a 32-bit unsigned integer into 4 little-endian bytes. -/
def leBytes32 (v : BitVec 32) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8]

/-- Serialize a 64-bit unsigned integer into 8 little-endian bytes. -/
def leBytes64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

namespace Syscall

/-- Dispatch a Linux AArch64 supervisor call (`SVC #0`, `arch/arm64/kernel/syscall.c:55`
    `el0_svc_common`) on `X8` over an explicit `(nr, handler)` table.
    - `[INTENTIONAL_SCOPE]`: Any syscall number absent from `table` fails closed with
      `.Exception "unmodeled syscall (svc)"`. -/
def dispatch (table : List (BitVec 64 × (State → State))) (s : State) : State :=
  match table.find? (·.1 == s.readReg64 Reg.x8) with
  | some (_, h) => h s
  | none        => s.setStatus (.Exception "unmodeled syscall (svc)")

end Syscall

end Arm64


