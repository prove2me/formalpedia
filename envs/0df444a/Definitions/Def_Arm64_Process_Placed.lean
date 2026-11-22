-- Prove2me | Definitions.Def_Arm64_Process_Placed
-- name    : Arm64_Process_Placed
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:20:02.857814+00:00
-- url     : https://prove2.me/theorems/f161da93-fcac-4f1b-9b3d-81cad37893c0
-- title:
--   Arm64.Trusted.Process.Placed — Placed Libraries in Linked ELF Executables
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Process/Placed.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Placed.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Process/Placed.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Process/Placed.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Process/Placed.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Process_Loader
public import Definitions.Def_Arm64_Object_Placed

/-!
# Placed Libraries in Linked ELF Executables (`Arm64.Obj.PlacedLib.InElf`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: When a parsed static ELF executable contains a placed library
  (`Obj.PlacedLib.InElf img lib pl`): the patched text and data bytes of `lib` under placement
  `pl` are mapped in `img`'s `PT_LOAD` segments (text executable, data readable, writable data
  writable), and each exported function has exactly one `.symtab` entry, at its placed address.
  `Obj.PlacedLib.LinkedAt lib elfBytes pl` says the raw ELF file `elfBytes` parses to such an
  image for the `Placeable` placement `pl`, and `Obj.PlacedLib.LinkedIn lib elfBytes` (`∃ pl,
  LinkedAt`) is the satisfiability (non-vacuity) witness for a layout-generic
  library contract (`Obj.PlacedLib.subroutineOk`) against a real linked binary.
  `InElf` constrains `pl.ρ` only through relocated text/data bytes and data-object placement: a
  spec mentioning `pl.ρ x` for a symbol no relocation or data object uses is not tied to the
  ELF's `.symtab`.
- **When to read**: Read when auditing a library's precondition-satisfiability statement or when
  composing a library contract into a whole-binary ELF proof.
-/

@[expose] public section

namespace Arm64.Obj

open Arm64.Process

/-- `img` maps `bytes` at `[addr, addr + bytes.length)` in its `PT_LOAD` segments: byte `i` is
    the byte at `addr + i` of the first segment containing that address (as in
    `ElfImage.loadState`), with a permission satisfying `ok`. -/
def ElfMaps (img : ElfImage) (addr : BitVec 64) (bytes : List (BitVec 8)) (ok : Perm → Bool) :
    Prop :=
  ∀ (i : Nat) (hi : i < bytes.length), ∃ p,
    Snapshot.cellAt img.segments (addr + BitVec.ofNat 64 i) = some (some p, bytes[i]) ∧ ok p

/-- The parsed executable `img` contains library `lib` placed under `pl`:
    - the patched text (`lib.text.patched pl`) is mapped executable (`r-x`) at `pl.base`;
    - each data object's initial bytes (`lib.patchedData pl d`) are mapped at `pl.ρ d.sym`,
      readable if `d.readOnly` and exactly `rw-` otherwise (as `↦ₛ` requires);
    - each exported function of `lib` has exactly one `.symtab` entry, at its placed address. -/
structure PlacedLib.InElf (img : ElfImage) (lib : PlacedLib) (pl : Placement) : Prop where
  text : ElfMaps img pl.base (lib.text.patched pl) (· == Perm.rx)
  data : ∀ d ∈ lib.data,
    ElfMaps img (pl.ρ d.sym) (lib.patchedData pl d) (fun p => if d.readOnly then p.r else p == Perm.rw)
  exports : ∀ e ∈ lib.exports, ∃ off, lookup e lib.text.symbols = some off ∧
    lookupUnique e img.symbols = some (pl.base + BitVec.ofNat 64 off)

/-- The ELF executable `elfBytes` links library `lib` at placement `pl`: it parses
    (`ElfImage.parse`) to an image containing `lib` under `pl`, and `lib` is `Placeable` at `pl`. -/
def PlacedLib.LinkedAt (lib : PlacedLib) (elfBytes : List (BitVec 8)) (pl : Placement) : Prop :=
  ∃ img, ElfImage.parse elfBytes = .ok img ∧ lib.Placeable pl ∧ lib.InElf img pl

/-- The ELF executable `elfBytes` links library `lib` at some placement (`PlacedLib.LinkedAt`). -/
abbrev PlacedLib.LinkedIn (lib : PlacedLib) (elfBytes : List (BitVec 8)) : Prop :=
  ∃ pl, lib.LinkedAt elfBytes pl

/-- The parsed executable `img` contains multi-block library `lib` placed under `mpl`:
    - every block `i`'s patched text (`lib.blocks[i].patched (lib.blockPlacement mpl i)`) is mapped
      executable (`r-x`) at `mpl.base i`;
    - each data object's initial bytes (`lib.patchedData mpl d`) are mapped at `mpl.ρ d.sym`,
      readable if `d.readOnly` and exactly `rw-` otherwise;
    - each exported function `e` of `lib` is defined in some block `i` at offset `off` and its
      raw name `lib.elfSym e` has exactly one `.symtab` entry, at `mpl.base i + off`. -/
structure MultiPlacedLib.InElf (img : ElfImage) (lib : MultiPlacedLib) (mpl : MultiPlacement) :
    Prop where
  blocks : ∀ (i : Nat) (hi : i < lib.blocks.length),
    ElfMaps img (mpl.base i) (lib.blocks[i].patched (lib.blockPlacement mpl i)) (· == Perm.rx)
  data : ∀ d ∈ lib.data,
    ElfMaps img (mpl.ρ d.sym) (lib.patchedData mpl d)
      (fun p => if d.readOnly then p.r else p == Perm.rw)
  exports : ∀ e ∈ lib.exports, ∃ i off,
    lookupBlockSym e lib.blocks = some (i, off) ∧
    lookupUnique (lib.elfSym e) img.symbols = some (mpl.base i + BitVec.ofNat 64 off)

/-- The ELF executable `elfBytes` links multi-block library `lib` at multi-block placement `mpl`:
    it parses (`ElfImage.parse`) to an image containing `lib` under `mpl`, and `lib` is
    `Placeable` at `mpl`. -/
def MultiPlacedLib.LinkedAt (lib : MultiPlacedLib) (elfBytes : List (BitVec 8))
    (mpl : MultiPlacement) : Prop :=
  ∃ img, ElfImage.parse elfBytes = .ok img ∧ lib.Placeable mpl ∧ lib.InElf img mpl

/-- The ELF executable `elfBytes` links multi-block library `lib` at some multi-block placement
    (`MultiPlacedLib.LinkedAt`). -/
abbrev MultiPlacedLib.LinkedIn (lib : MultiPlacedLib) (elfBytes : List (BitVec 8)) : Prop :=
  ∃ mpl, lib.LinkedAt elfBytes mpl

end Arm64.Obj


