-- Prove2me | Definitions.Def_Arm64_Syscalls
-- name    : Arm64_Syscalls
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:11:05.992923+00:00
-- url     : https://prove2.me/theorems/a91606b6-0c18-42c2-9cb6-dfafb8583c69
-- title:
--   Arm64.Trusted.Syscalls — Linux AArch64 Syscall Families Umbrella
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common
public import Definitions.Def_Arm64_Syscalls_Stdio
public import Definitions.Def_Arm64_Syscalls_FileIo
public import Definitions.Def_Arm64_Syscalls_Poll
public import Definitions.Def_Arm64_Syscalls_Alloc
public import Definitions.Def_Arm64_Syscalls_Signals
public import Definitions.Def_Arm64_Syscalls_Time
public import Definitions.Def_Arm64_Syscalls_Random
public import Definitions.Def_Arm64_Syscalls_Misc

/-!
# Linux AArch64 Syscall Families Umbrella (`Arm64.Trusted.Syscalls`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Re-exports the modular Linux AArch64 syscall families under
  `Arm64/Trusted/Syscalls/` (`Common`, `Stdio`, `FileIo`, `Poll`, `Alloc`, `Signals`, `Time`,
  `Random`, `Misc`) and defines the empty bundle `Syscall.none`, the full 32-entry dispatch table
  `Syscall.standardTable`, `Syscall.standard`, and the compatibility alias `execSyscall`.
- **When to read**: Read `Arm64/Trusted/Syscalls/README.md` to pick the minimal bundle for a
  specification (`noSyscalls`, `Syscall.stdioCli`, `Syscall.fileIo`, ...) so unused syscall families
  stay outside the theorem statement's transitive constant closure.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Empty dispatch table: every `SVC #0` fails closed with `.Exception "unmodeled syscall (svc)"`. -/
def none : State → State := dispatch []

/-- Complete 32-syscall Linux AArch64 dispatch table combining all modeled families. -/
def standardTable : List (BitVec 64 × (State → State)) :=
  stdioTable ++ fileIoOnlyTable ++ pollTable ++ allocTable ++ signalsTable ++ timeTable ++ randomTable ++ miscTable

/-- Full modeled Linux AArch64 syscall bundle (`32` syscalls across `Stdio`, `FileIo`, `Poll`,
    `Alloc`, `Signals`, `Time`, `Random`, and `Misc`). -/
def standard : State → State := dispatch standardTable

end Syscall

/-- Compatibility alias for `Syscall.standard` (`SVC #0` dispatch over all 32 modeled syscalls). -/
abbrev execSyscall : State → State := Syscall.standard

end Arm64


