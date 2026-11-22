-- Prove2me | Definitions.Def_Arm64_Syscalls_Random
-- name    : Arm64_Syscalls_Random
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:10:29.684236+00:00
-- url     : https://prove2.me/theorems/227fa632-971e-492f-8b10-337c53388b66
-- title:
--   Arm64.Trusted.Syscalls.Random — Entropy Syscalls
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Syscalls/Random.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Random.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Syscalls/Random.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Syscalls/Random.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Syscalls/Random.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Syscalls_Common
public import Definitions.Def_Arm64_Syscalls_Drivers_Random

/-!
# Entropy Syscalls

Re-exports `Arm64.Trusted.Syscalls.Drivers.Random` (`drivers/char/random.c`: `getrandom`) and
defines the single-syscall dispatch table `Syscall.randomTable` and handler `Syscall.random`.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for kernel randomness (`getrandom`). -/
def randomTable : List (BitVec 64 × (State → State)) :=
  [(SYS_GETRANDOM, execGetrandom)]

/-- Syscall bundle permitting `getrandom`. -/
def random : State → State := dispatch randomTable

end Syscall

end Arm64


