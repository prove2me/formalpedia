-- Prove2me | Definitions.Def_Arm64_Object_Reloc
-- name    : Arm64_Object_Reloc
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:11:50.132403+00:00
-- url     : https://prove2.me/theorems/724e28f6-7943-4475-af3f-e18ed866094f
-- title:
--   Arm64.Trusted.Object.Reloc — AArch64 ELF Relocations and Immediate Range Helpers
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Object/Reloc.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Reloc.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Object/Reloc.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Reloc.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Object/Reloc.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

/-!
# AArch64 ELF Relocations and Immediate Range Helpers

Static AArch64 ELF relocation classes (`RelocKind`), relocation entries (`RelocEntry`),
link-independent code and data symbol records (`SymCodeInfo`, `SymDataInfo`), little-endian
byte/word helpers, and instruction-word patchers with immediate range and alignment predicates.
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Little-endian byte, page, and association-list helpers -/

/-- Page size (4096 bytes on AArch64). -/
def pageSize : Nat := 4096

/-- Little-endian bytes of a 64-bit value. -/
def bytesLE (n : Nat) (v : BitVec 64) : List (BitVec 8) :=
  (List.range n).map fun i => v.extractLsb' (8 * i) 8

/-- Page address (`x & ~0xfff`), clearing the low 12 bits. -/
def pageOf (x : BitVec 64) : BitVec 64 := x &&& 0xfffffffffffff000#64

/-- Intra-page 12-bit offset (`x & 0xfff`). -/
def lo12Of (x : BitVec 64) : BitVec 64 := x &&& 0xfff#64

/-- Read a 32-bit little-endian word from `xs` at byte offset `off` (0-padded if out of bounds). -/
def wordOfBytesLE (xs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  let b0 := (xs.getD off 0#8).zeroExtend 32
  let b1 := (xs.getD (off + 1) 0#8).zeroExtend 32 <<< 8
  let b2 := (xs.getD (off + 2) 0#8).zeroExtend 32 <<< 16
  let b3 := (xs.getD (off + 3) 0#8).zeroExtend 32 <<< 24
  b0 ||| b1 ||| b2 ||| b3

/-- 4-byte little-endian encoding of a 32-bit word `w`. -/
def bytesOfWordLE (w : BitVec 32) : List (BitVec 8) :=
  bytesLE 4 (w.zeroExtend 64)

/-- Look up `name` in an association list (first occurrence). -/
def lookup {α} (name : String) (xs : List (String × α)) : Option α :=
  (xs.find? (·.1 == name)).map (·.2)

/-- Unique-occurrence lookup (`some v` iff `name` appears in `xs` exactly once). -/
def lookupUnique {α} (name : String) (xs : List (String × α)) : Option α :=
  match xs.filter (·.1 == name) with
  | [(_, v)] => some v
  | _ => none

/-- `bs` occurs in `xs` at offset `off`. -/
def bytesAt (xs : List (BitVec 8)) (off : Nat) (bs : List (BitVec 8)) : Bool :=
  off + bs.length ≤ xs.length && (xs.drop off).take bs.length == bs

/-! ## Relocation classes and symbol records -/

/-- AArch64 ELF static relocation classes supported by layout-generic objects. -/
inductive RelocKind where
  | call26
  | jump26
  | adrpHi21
  | adrpHi21Nc
  | addLo12
  | ldst8Lo12
  | ldst16Lo12
  | ldst32Lo12
  | ldst64Lo12
  | ldst128Lo12
  | condbr19
  | tstbr14
  | ldPrelLo19
  | adrPrelLo21
  | prel32
  | abs64
  | abs32
  | adrGotPage
  | ld64GotLo12Nc
  | tlsieAdrGottprelPage21
  | tlsieLd64GottprelLo12Nc
  | tlsdescAdrPage21
  | tlsdescLd64Lo12
  | tlsdescAddLo12
  | tlsdescCall
  | tlsleAddTprelHi12
  | tlsleAddTprelLo12
  | tlsleAddTprelLo12Nc
  | tlsleLdst8TprelLo12Nc
  | tlsleLdst16TprelLo12Nc
  | tlsleLdst32TprelLo12Nc
  | tlsleLdst64TprelLo12Nc
  | tlsleLdst128TprelLo12Nc
  | tlsleMovwTprelG1
  | tlsleMovwTprelG1Nc
  | tlsleMovwTprelG0
  | tlsleMovwTprelG0Nc
  deriving DecidableEq, Repr, Inhabited

/-- Whether `kind` is a GOT or initial-exec TLS relocation class. -/
def RelocKind.isGotOrTlsIe : RelocKind → Bool
  | .adrGotPage | .ld64GotLo12Nc
  | .tlsieAdrGottprelPage21 | .tlsieLd64GottprelLo12Nc => true
  | _ => false

/-- One relocation at byte offset `off` within a function or data symbol, targeting `sym + addend`.
    When `localSym = true`, `sym` is resolved exclusively in the defining object's symbol table
    (`STB_LOCAL`). -/
structure RelocEntry where
  off : Nat
  kind : RelocKind
  sym : String
  addend : Int := 0
  localSym : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Link-independent facts about one function with general code relocations (`relocFns`). -/
structure SymCodeInfo where
  sym : String
  code : List (BitVec 8)
  relocs : List RelocEntry := []
  deriving DecidableEq, Repr, Inhabited

/-- Link-independent facts about one `.rodata`, `.data`, `.data.rel.ro`, or `.bss` symbol (`dataSyms`). -/
structure SymDataInfo where
  sym : String
  align : Nat := 1
  readOnly : Bool := true
  bytes : List (BitVec 8) := []
  zeroTail : Nat := 0
  relocs : List RelocEntry := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Instruction word patchers and range predicates -/

/-- Whether a 26-bit PC-relative branch (`B`/`BL`) from `placeOff` to `targetOff` is 4-byte
    aligned and within the signed 28-bit byte range `[-2^27, 2^27)`. -/
def branchInRange (placeOff targetOff : Nat) : Bool :=
  let d : BitVec 64 := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  d.toNat % 4 == 0 && decide (-(2 ^ 27 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 27 : Int))

/-- Patch the 26-bit branch immediate of a 4-byte little-endian instruction `w` (preserving the
    top 6 opcode bits of `w[3]`) for a branch from `placeOff` to `targetOff`. -/
def patchBranchBytes (w : List (BitVec 8)) (placeOff targetOff : Nat) : List (BitVec 8) :=
  let d : BitVec 64 := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  let hi := (w.getD 3 0#8 &&& 0xfc#8).zeroExtend 64 <<< 24
  let imm := (d >>> 2) &&& 0x03ffffff#64
  bytesLE 4 (hi ||| imm)

/-- Patch 32-bit instruction template `w` for a 26-bit branch (`B`/`BL`) from `place` to `target`. -/
def branchWord (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
  (w &&& 0xfc000000#32) ||| (((target - place) >>> 2).setWidth 32 &&& 0x03ffffff#32)

/-- Propositional range condition for a 26-bit PC-relative branch (`B`/`BL`). -/
def BranchInRange (place target : BitVec 64) : Prop :=
  (target - place).toNat % 4 = 0 ∧
  -(2 ^ 27 : Int) ≤ (target - place).toInt ∧ (target - place).toInt < (2 ^ 27 : Int)

/-- Patch 32-bit `ADRP` template `w` with page displacement `pgOff = pageOf target - pageOf place`. -/
def adrpWordOff (w : BitVec 32) (pgOff : BitVec 64) : BitVec 32 :=
  (w &&& 0x9f00001f#32) |||
    ((((pgOff >>> 12).setWidth 32 &&& 0x3#32) <<< 29) |||
     (((pgOff >>> 14).setWidth 32 &&& 0x7ffff#32) <<< 5))

/-- Patch 32-bit `ADRP` template `w` at `place` targeting `target`. -/
def adrpWord (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
  adrpWordOff w (pageOf target - pageOf place)

/-- Propositional range condition (`[-4 GiB, 4 GiB)`) for `R_AARCH64_ADR_PREL_PG_HI21` / `R_AARCH64_ADR_GOT_PAGE`. -/
def AdrpInRange (place target : BitVec 64) : Prop :=
  -(2 ^ 32 : Int) ≤ (pageOf target - pageOf place).toInt ∧
  (pageOf target - pageOf place).toInt < (2 ^ 32 : Int)

/-- Decidable range check (`[-4 GiB, 4 GiB)`) for `R_AARCH64_ADR_PREL_PG_HI21` / `R_AARCH64_ADR_GOT_PAGE`. -/
def adrpInRange (placeOff targetOff : Nat) : Bool :=
  let pgOff := pageOf (BitVec.ofNat 64 targetOff) - pageOf (BitVec.ofNat 64 placeOff)
  decide (-(2 ^ 32 : Int) ≤ pgOff.toInt) && decide (pgOff.toInt < (2 ^ 32 : Int))

/-- Patch 32-bit `ADR` template `w` with byte displacement `d = target - place`. -/
def adrWordOff (w : BitVec 32) (d : BitVec 64) : BitVec 32 :=
  (w &&& 0x9f00001f#32) |||
    (((d.setWidth 32 &&& 0x3#32) <<< 29) |||
     (((d >>> 2).setWidth 32 &&& 0x7ffff#32) <<< 5))

/-- Patch 32-bit `ADR` template `w` at `place` targeting `target`. -/
def adrWord (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
  adrWordOff w (target - place)

/-- Propositional range condition (`[-1 MiB, 1 MiB)`) for `R_AARCH64_ADR_PREL_LO21`. -/
def AdrInRange (place target : BitVec 64) : Prop :=
  -(2 ^ 20 : Int) ≤ (target - place).toInt ∧ (target - place).toInt < (2 ^ 20 : Int)

/-- Decidable range check (`[-1 MiB, 1 MiB)`) for `R_AARCH64_ADR_PREL_LO21`. -/
def adrInRange (placeOff targetOff : Nat) : Bool :=
  let d := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  decide (-(2 ^ 20 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 20 : Int))

/-- Patch 32-bit `:lo12:` instruction template `w` (`ADD` or scaled `LDR`/`STR` with shift `scale`). -/
def lo12Word (scale : Nat) (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  (w &&& 0xffc003ff#32) |||
    ((((target &&& 0xfff#64) >>> scale).setWidth 32 &&& 0xfff#32) <<< 10)

/-- Low-bit alignment mask `(1 <<< scale) - 1` for scaled `:lo12:` load/store relocations. -/
def lo12AlignMask : Nat → BitVec 64
  | 0 => 0#64
  | 1 => 1#64
  | 2 => 3#64
  | 3 => 7#64
  | _ => 15#64

/-- Propositional alignment condition for a `2^scale`-byte scaled `:lo12:` relocation. -/
def Lo12Aligned (scale : Nat) (target : BitVec 64) : Prop :=
  (target &&& lo12AlignMask scale) = 0#64

/-- Decidable alignment check for a `2^scale`-byte scaled `:lo12:` relocation. -/
def lo12Aligned (scale : Nat) (targetOff : Nat) : Bool :=
  (BitVec.ofNat 64 targetOff &&& lo12AlignMask scale) == 0#64

/-- Patch 32-bit 19-bit PC-relative instruction template `w` (`B.cond`, `CBZ`/`CBNZ`, `LDR` literal). -/
def imm19WordOff (w : BitVec 32) (d : BitVec 64) : BitVec 32 :=
  (w &&& 0xff00001f#32) ||| (((d >>> 2).setWidth 32 &&& 0x7ffff#32) <<< 5)

/-- Patch 32-bit 19-bit PC-relative instruction template `w` at `place` targeting `target`. -/
def imm19Word (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
  imm19WordOff w (target - place)

/-- Propositional range condition (`[-1 MiB, 1 MiB)`, 4-byte aligned) for `CONDBR19` / `LD_PREL_LO19`. -/
def Imm19InRange (place target : BitVec 64) : Prop :=
  (target - place).toNat % 4 = 0 ∧
  -(2 ^ 20 : Int) ≤ (target - place).toInt ∧ (target - place).toInt < (2 ^ 20 : Int)

/-- Decidable range check (`[-1 MiB, 1 MiB)`, 4-byte aligned) for `CONDBR19` / `LD_PREL_LO19`. -/
def imm19InRange (placeOff targetOff : Nat) : Bool :=
  let d := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  d.toNat % 4 == 0 && decide (-(2 ^ 20 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 20 : Int))

/-- Patch 32-bit 14-bit PC-relative test-and-branch template `w` (`TBZ`/`TBNZ`). -/
def tstbr14WordOff (w : BitVec 32) (d : BitVec 64) : BitVec 32 :=
  (w &&& 0xfff8001f#32) ||| (((d >>> 2).setWidth 32 &&& 0x3fff#32) <<< 5)

/-- Patch 32-bit 14-bit PC-relative test-and-branch template `w` at `place` targeting `target`. -/
def tstbr14Word (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
  tstbr14WordOff w (target - place)

/-- Propositional range condition (`[-32 KiB, 32 KiB)`, 4-byte aligned) for `R_AARCH64_TSTBR14`. -/
def TstBr14InRange (place target : BitVec 64) : Prop :=
  (target - place).toNat % 4 = 0 ∧
  -(2 ^ 15 : Int) ≤ (target - place).toInt ∧ (target - place).toInt < (2 ^ 15 : Int)

/-- Decidable range check (`[-32 KiB, 32 KiB)`, 4-byte aligned) for `R_AARCH64_TSTBR14`. -/
def tstbr14InRange (placeOff targetOff : Nat) : Bool :=
  let d := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  d.toNat % 4 == 0 && decide (-(2 ^ 15 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 15 : Int))

/-- Propositional range condition (`[-2 GiB, 2 GiB)`) for `R_AARCH64_PREL32`. -/
def Prel32InRange (place target : BitVec 64) : Prop :=
  -(2 ^ 31 : Int) ≤ (target - place).toInt ∧ (target - place).toInt < (2 ^ 31 : Int)

/-- Decidable range check (`[-2 GiB, 2 GiB)`) for `R_AARCH64_PREL32`. -/
def prel32InRange (placeOff targetOff : Nat) : Bool :=
  let d := BitVec.ofNat 64 targetOff - BitVec.ofNat 64 placeOff
  decide (-(2 ^ 31 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 31 : Int))

/-- Propositional range condition for `R_AARCH64_ABS32`. -/
def Abs32InRange (target : BitVec 64) : Prop :=
  -(2 ^ 31 : Int) ≤ target.toInt ∧ target.toInt < (2 ^ 32 : Int)

/-- `w` is a 64-bit unsigned-offset `LDR Xt, [Xn, #pimm]` (`11 111 0 01 01 imm12 Rn Rt`). -/
def isLdr64UnsignedWord (w : BitVec 32) : Bool := (w &&& 0xffc00000#32) == 0xf9400000#32

/-- Convert a 64-bit `LDR Xt, [Xn, #0]` template `w` into `ADD Xd, Xn, #0` (preserving `Rn` and `Rd`). -/
def ldrToAddWord (w : BitVec 32) : BitVec 32 := 0x91000000#32 ||| (w &&& 0x3ff#32)

/-- Relax `R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` (`ADRP Xd, :gottprel:sym`) to
    `MOVZ Xd, #:tprel_g1:target, LSL #16` (`0xd2a00000 | Rd | (((target >> 16) & 0xffff) << 5)`). -/
def tlsieMovzWord (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  0xd2a00000#32 ||| (w &&& 0x1f#32) ||| (((target >>> 16).setWidth 32 &&& 0xffff#32) <<< 5)

/-- Relax `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` (`LDR Xd, [Xn, :gottprel_lo12:sym]`) to
    `MOVK Xd, #:tprel_g0_nc:target` (`0xf2800000 | Rd | ((target & 0xffff) << 5)`). -/
def tlsieMovkWord (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  0xf2800000#32 ||| (w &&& 0x1f#32) ||| ((target.setWidth 32 &&& 0xffff#32) <<< 5)

/-- Propositional 32-bit unsigned TP-offset range (`[0, 2^32)`) for IE-to-LE TLS relaxation. -/
def TlsIeInRange (target : BitVec 64) : Prop :=
  target.toNat < 2 ^ 32

/-- Decidable 32-bit unsigned TP-offset range check (`[0, 2^32)`) for IE-to-LE TLS relaxation. -/
def tlsIeInRange (targetOff : Nat) : Bool :=
  targetOff < 2 ^ 32

/-- Apply a signed byte `addend` to a non-negative symbol offset `off`, returning `some targetOff`
    when `0 ≤ (off : Int) + addend < 2^64`. -/
def addSignedOff (off : Nat) (addend : Int) : Option Nat :=
  let t : Int := (off : Int) + addend
  if 0 ≤ t && t < (2 ^ 64 : Int) then some t.toNat else none

/-- Whether code relocation `kind` at offset `placeOff` targeting `targetOff` satisfies its
    alignment and range side conditions. -/
def codeRelocInRange (kind : RelocKind) (placeOff targetOff : Nat) : Bool :=
  match kind with
  | .call26 | .jump26 => branchInRange placeOff targetOff
  | .adrpHi21 | .adrGotPage | .tlsieAdrGottprelPage21 => adrpInRange placeOff targetOff
  | .adrpHi21Nc => true
  | .addLo12 | .ldst8Lo12 => true
  | .ldst16Lo12 => lo12Aligned 1 targetOff
  | .ldst32Lo12 => lo12Aligned 2 targetOff
  | .ldst64Lo12 | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc => lo12Aligned 3 targetOff
  | .ldst128Lo12 => lo12Aligned 4 targetOff
  | .condbr19 | .ldPrelLo19 => imm19InRange placeOff targetOff
  | .tstbr14 => tstbr14InRange placeOff targetOff
  | .adrPrelLo21 => adrInRange placeOff targetOff
  | .prel32 => prel32InRange placeOff targetOff
  | .abs64 | .abs32 => false
  | _ => false

/-- Patch 32-bit instruction template `w` at `placeOff` for relocation `kind` targeting `targetOff`. -/
def patchCodeRelocWord (kind : RelocKind) (w : BitVec 32) (placeOff targetOff : Nat) : BitVec 32 :=
  let place := BitVec.ofNat 64 placeOff
  let target := BitVec.ofNat 64 targetOff
  match kind with
  | .call26 | .jump26 => branchWord w place target
  | .adrpHi21 | .adrpHi21Nc
  | .adrGotPage | .tlsieAdrGottprelPage21 => adrpWord w place target
  | .addLo12 | .ldst8Lo12 => lo12Word 0 w target
  | .ldst16Lo12 => lo12Word 1 w target
  | .ldst32Lo12 => lo12Word 2 w target
  | .ldst64Lo12 | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc => lo12Word 3 w target
  | .ldst128Lo12 => lo12Word 4 w target
  | .condbr19 | .ldPrelLo19 => imm19Word w place target
  | .tstbr14 => tstbr14Word w place target
  | .adrPrelLo21 => adrWord w place target
  | .prel32 => (target - place).setWidth 32
  | .abs64 | .abs32 => w
  | _ => 0#32

end Arm64.Obj


