-- Prove2me | Definitions.Def_Arm64
-- name    : Arm64
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:16:32.755775+00:00
-- url     : https://prove2.me/theorems/81796d1e-b51c-4632-b7fb-96468208db58
-- title:
--   Arm64.Trusted — Trusted Computing Base
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
Also removed `import Arm64.Trusted.Surface.Abi` (Surface syntax layer, not published).
Also removed `import Arm64.Trusted.Surface.CType` (Surface syntax layer, not published).
Also removed `import Arm64.Trusted.Surface.HexCode` (Surface syntax layer, not published).
Also removed `import Arm64.Trusted.Surface.Ascii` (Surface syntax layer, not published).
No other change.
-/

-- Layer 1 (`Arm64/Trusted/ISA/`): instruction-level AArch64 semantics
module

public import Definitions.Def_Arm64_ISA_Syntax
public import Definitions.Def_Arm64_ISA_Decode
public import Definitions.Def_Arm64_ISA_Memory
public import Definitions.Def_Arm64_ISA_State
public import Definitions.Def_Arm64_ISA_Float
public import Definitions.Def_Arm64_ISA_Eval
public import Definitions.Def_Arm64_Syscalls
public import Definitions.Def_Arm64_ISA_Semantics

-- Layer 2 (`Arm64/Trusted/Object/`): relocatable ELF object relocations, placement, and pre-link label provenance
public import Definitions.Def_Arm64_Object_Reloc
public import Definitions.Def_Arm64_Object_Placed
public import Definitions.Def_Arm64_Object_Labels

-- Layer 3 (`Arm64/Trusted/Spec/`): `Init`-only machine-level specification foundation
public import Definitions.Def_Arm64_Spec_AsciiNum
public import Definitions.Def_Arm64_Spec_RustAbi
public import Definitions.Def_Arm64_Spec_RustRuntime
public import Definitions.Def_Arm64_Spec_SepLogic
public import Definitions.Def_Arm64_Spec_Hoare
public import Definitions.Def_Arm64_Spec_Placed

-- Layer 4 (`Arm64/Trusted/Surface/`): surface specification DSLs and literal macros

/-!
# Trusted Computing Base

Umbrella module re-exporting the trusted AArch64 ISA semantics (`Arm64/Trusted/ISA/`), Linux
syscall interface (`Arm64/Trusted/Syscalls/`), ELF object relocation and placement model
(`Arm64/Trusted/Object/`), machine-level specification foundation (`Arm64/Trusted/Spec/`), and
surface specification macros (`Arm64/Trusted/Surface/`). Process-image byte loaders
(`IncludeBytes`, `FileBytes`) are imported via `Arm64.Trusted.Process`, and heap/allocator models
(`RustHeap`, `GlobalAlloc`) are imported directly by the specifications that use them.
-/

@[expose] public section


