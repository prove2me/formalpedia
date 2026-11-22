-- Prove2me | Definitions.Def_Arm64_Process
-- name    : Arm64_Process
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:18:51.237245+00:00
-- url     : https://prove2.me/theorems/17342a41-512e-41e0-91bc-0ce0db595aba
-- title:
--   Arm64.Trusted.Process — Trusted Static ELF64 Process Semantics
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also removed `import Arm64.Trusted.Surface.FileBytes` (Surface syntax layer, not published).
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Types
public import Definitions.Def_Arm64_Process_Assumptions
public import Definitions.Def_Arm64_Process_Loader
public import Definitions.Def_Arm64_Process_Semantics

/-!
# Trusted Static ELF64 Process Semantics

Re-exports `Arm64.Trusted.Process.Types`, `Arm64.Trusted.Process.Assumptions`,
`Arm64.Trusted.Process.Loader`, `Arm64.Trusted.Process.Semantics`, and the compile-time
`file_bytes% "path" sha256 "<hex>"` elaborator (`Arm64.Trusted.Surface.FileBytes`). Kept separate
from `Arm64/Trusted.lean` so subroutine-level specifications do not depend on the whole-binary
ELF64 loader.

Library-level and hook-override modules (`Arm64.Trusted.Process.Placed`,
`Arm64.Trusted.Process.OverrideWellBehaved`, and `Arm64.Trusted.Process.Overrides`) are omitted
from this barrel so whole-process specifications without library contracts or overrides remain
independent of Hoare and separation-logic definitions.
-/

@[expose] public section


