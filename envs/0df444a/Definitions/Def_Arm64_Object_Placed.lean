-- Prove2me | Definitions.Def_Arm64_Object_Placed
-- name    : Arm64_Object_Placed
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:12:22.034714+00:00
-- url     : https://prove2.me/theorems/54c44d66-86c5-40fe-a966-f95a39a97ae5
-- title:
--   Arm64.Trusted.Object.Placed — Placed Libraries: Layout-Generic Relocatable Code
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Object/Placed.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Placed.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Object/Placed.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Placed.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Object/Placed.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Object_Reloc
public import Definitions.Def_Arm64_ISA_Semantics

/-!
# Placed Libraries: Layout-Generic Relocatable Code

Models a library as relocatable object code and data before linking (`Obj.CodeBlock`,
`Obj.PlacedLib`, `Obj.MultiPlacedLib`), byte-slice memory mapping (`Obj.HoldsBytes`), and the
output of a static linker (`ld.lld`) placing code at `base` and resolving external and data
symbols through `ρ` (`Obj.Placement`, `Obj.PlacedLib.Placeable`, `Obj.CodeBlock.patched`,
`Obj.PlacedLib.program`, `Obj.PlacedLib.patchedData`). Covers AArch64 `ADRP`+`ADD` to `NOP`+`ADR`,
GOT, and TLS linker relaxations (`Placement.relax`), branch-to-branch retargeting
(`Placement.b2b`), and undefined weak references (`Placement.undefWeak`).

## Model
A `PlacedLib` is one rigid text block (`CodeBlock`: the concatenated `.text*` input sections of
the library's objects, in link order, with alignment padding) plus data objects (`SymDataInfo`:
one per `.rodata`/`.data`/`.bss` input section or merged-section piece). A `Placement` chooses:
- `base`: the text block's address (no page alignment is assumed);
- `ρ`: the address of every symbol *not* defined in the block (data objects, extern functions);
- `relax`: for each relaxable `ADRP`+`ADD` pair (by `ADRP` byte offset), whether the linker
  relaxed it;
- `b2b`: for each branch whose target is a block `B`, whether the linker retargeted it to that
  `B`'s target;
- `undefWeak`: for each weak reference (`CodeBlock.weakRefs`), whether the linker left it
  undefined (direct branches to it then branch to the next instruction).
Every code relocation (including branches inside the block) is applied by `CodeBlock.patched`
with targets `addSignedAddr (resolve sym) addend`. `Placeable` collects the conditions under
which a linker applies the relocations without overflow; a contract over `PlacedLib.program`
assuming `Placeable` holds for every such link. Whether some real binary is such a link is a
separate, checkable fact (`Obj.PlacedLib.InElf`).

## Auditing
Soundness of a library theorem about a real binary rests only on `PlacedLib.program`,
`PlacedLib.fnAddr`, `PlacedLib.dataInit` and `PlacedLib.InElf` (bytes and permissions in the
ELF). The relocation, relaxation and branch-to-branch model (`patchedWord`, `Placeable`) only
affects completeness: if it disagrees with what the linker emitted, `InElf` fails on the real
bytes (or the theorem is harder to prove), but it cannot make a false claim about those bytes.
-/

@[expose] public section

namespace Arm64.Obj

/-! ## Relocation word patching -/

/-- The `NOP` instruction word (`0xd503201f`). -/
def nopWord : BitVec 32 := 0xd503201f#32

/-- `R_AARCH64_TLSDESC_ADR_PAGE21` relaxed to Local-Exec (`TLSLE`):
    `movz x0, #((target >> 16) & 0xffff), lsl #16`. -/
def tlsdescAdrPage21Word (target : BitVec 64) : BitVec 32 :=
  0xd2a00000#32 ||| (((target >>> 16).setWidth 32 &&& 0xffff#32) <<< 5)

/-- `R_AARCH64_TLSDESC_LD64_LO12` relaxed to Local-Exec (`TLSLE`):
    `movk x0, #(target & 0xffff)`. -/
def tlsdescLd64Lo12Word (target : BitVec 64) : BitVec 32 :=
  0xf2800000#32 ||| ((target.setWidth 32 &&& 0xffff#32) <<< 5)

/-- Patch 32-bit `ADD Xd, Xn, #imm12, lsl #12` template `w` for `R_AARCH64_TLSLE_ADD_TPREL_HI12`. -/
def tprelHi12Word (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  (w &&& 0xffc003ff#32) ||| (((target >>> 12).setWidth 32 &&& 0xfff#32) <<< 10)

/-- Patch 32-bit `MOVZ`/`MOVN` template `w` with signed `target` shifted right by `shift` bits
    (`R_AARCH64_TLSLE_MOVW_TPREL_G1` at `shift = 16`, `R_AARCH64_TLSLE_MOVW_TPREL_G0` at `shift = 0`):
    sets bit 30 (`MOVZ`) when `0 ≤ target.toInt`, or clears bit 30 (`MOVN`) and encodes `~~~target`
    when `target.toInt < 0`. -/
def movwSignedWord (shift : Nat) (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  if 0 ≤ target.toInt then
    let imm16 : BitVec 32 := ((target >>> shift).setWidth 32) &&& 0xffff#32
    ((w &&& 0xbfe0001f#32) ||| 0x40000000#32) ||| (imm16 <<< 5)
  else
    let imm16 : BitVec 32 := (((~~~target) >>> shift).setWidth 32) &&& 0xffff#32
    (w &&& 0xbfe0001f#32) ||| (imm16 <<< 5)

/-- Patch 32-bit `MOVK` template `w` with unchecked 16-bit slice `target >>> shift`
    (`R_AARCH64_TLSLE_MOVW_TPREL_G1_NC` at `shift = 16`, `R_AARCH64_TLSLE_MOVW_TPREL_G0_NC` at `shift = 0`). -/
def movwNcWord (shift : Nat) (w : BitVec 32) (target : BitVec 64) : BitVec 32 :=
  let imm16 : BitVec 32 := ((target >>> shift).setWidth 32) &&& 0xffff#32
  (w &&& 0xffe0001f#32) ||| (imm16 <<< 5)

/-- Propositional range condition (`[0, 2^32)`) for `TLSDESC → TLSLE` relaxation. -/
def TlsUInt32InRange (target : BitVec 64) : Prop :=
  0 ≤ target.toInt ∧ target.toInt < (2 ^ 32 : Int)

/-- Propositional range condition (`[0, 2^24)`) for `R_AARCH64_TLSLE_ADD_TPREL_HI12`. -/
def TprelHi12InRange (target : BitVec 64) : Prop :=
  0 ≤ target.toInt ∧ target.toInt < (2 ^ 24 : Int)

/-- Propositional range condition (`[0, 2^12)`) for `R_AARCH64_TLSLE_ADD_TPREL_LO12`. -/
def TprelLo12InRange (target : BitVec 64) : Prop :=
  0 ≤ target.toInt ∧ target.toInt < (2 ^ 12 : Int)

/-- Propositional signed range condition (`[-2^32, 2^32)`) for `R_AARCH64_TLSLE_MOVW_TPREL_G1`. -/
def TprelG1InRange (target : BitVec 64) : Prop :=
  -(2 ^ 32 : Int) ≤ target.toInt ∧ target.toInt < (2 ^ 32 : Int)

/-- Propositional signed range condition (`[-2^16, 2^16)`) for `R_AARCH64_TLSLE_MOVW_TPREL_G0`. -/
def TprelG0InRange (target : BitVec 64) : Prop :=
  -(2 ^ 16 : Int) ≤ target.toInt ∧ target.toInt < (2 ^ 16 : Int)

/-- AArch64 ELF TLS Variant I base offset after the 16-byte (2-pointer) TCB header,
    aligned up to `max 1 maxTlsAlign`: `alignUp 16 (max 1 maxTlsAlign)`. -/
def tlsBaseOffset (maxTlsAlign : Nat) : Nat :=
  let a := Nat.max 1 maxTlsAlign
  ((15 + a) / a) * a

/-- Propositional range/alignment condition for a general code relocation `kind` at `place`
    targeting `target`. -/
def CodeRelocInRange (kind : RelocKind) (place target : BitVec 64) : Prop :=
  match kind with
  | .call26 | .jump26 => BranchInRange place target
  | .adrpHi21 | .adrGotPage | .tlsieAdrGottprelPage21 => AdrpInRange place target
  | .adrpHi21Nc => True
  | .addLo12 | .ldst8Lo12 => True
  | .ldst16Lo12 => Lo12Aligned 1 target
  | .ldst32Lo12 => Lo12Aligned 2 target
  | .ldst64Lo12 | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc => Lo12Aligned 3 target
  | .ldst128Lo12 => Lo12Aligned 4 target
  | .condbr19 | .ldPrelLo19 => Imm19InRange place target
  | .tstbr14 => TstBr14InRange place target
  | .adrPrelLo21 => AdrInRange place target
  | .prel32 => Prel32InRange place target
  | .abs64 | .abs32 => False
  | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall => TlsUInt32InRange target
  | .tlsleAddTprelHi12 => TprelHi12InRange target
  | .tlsleAddTprelLo12 => TprelLo12InRange target
  | .tlsleAddTprelLo12Nc | .tlsleLdst8TprelLo12Nc => True
  | .tlsleLdst16TprelLo12Nc => Lo12Aligned 1 target
  | .tlsleLdst32TprelLo12Nc => Lo12Aligned 2 target
  | .tlsleLdst64TprelLo12Nc => Lo12Aligned 3 target
  | .tlsleLdst128TprelLo12Nc => Lo12Aligned 4 target
  | .tlsleMovwTprelG1 => TprelG1InRange target
  | .tlsleMovwTprelG1Nc => True
  | .tlsleMovwTprelG0 => TprelG0InRange target
  | .tlsleMovwTprelG0Nc => True

/-- Patch a 32-bit instruction template `w` at address `place` for relocation `kind` targeting
    address `target`. -/
def patchRelocWord (kind : RelocKind) (w : BitVec 32) (place target : BitVec 64) : BitVec 32 :=
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
  | .tlsdescAdrPage21 => tlsdescAdrPage21Word target
  | .tlsdescLd64Lo12 => tlsdescLd64Lo12Word target
  | .tlsdescAddLo12 | .tlsdescCall => nopWord
  | .tlsleAddTprelHi12 => tprelHi12Word w target
  | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc | .tlsleLdst8TprelLo12Nc => lo12Word 0 w target
  | .tlsleLdst16TprelLo12Nc => lo12Word 1 w target
  | .tlsleLdst32TprelLo12Nc => lo12Word 2 w target
  | .tlsleLdst64TprelLo12Nc => lo12Word 3 w target
  | .tlsleLdst128TprelLo12Nc => lo12Word 4 w target
  | .tlsleMovwTprelG1 => movwSignedWord 16 w target
  | .tlsleMovwTprelG1Nc => movwNcWord 16 w target
  | .tlsleMovwTprelG0 => movwSignedWord 0 w target
  | .tlsleMovwTprelG0Nc => movwNcWord 0 w target

/-- Compute `symAddr + addend` in 64-bit two's-complement arithmetic (`symAddr` when `addend = 0`). -/
def addSignedAddr (symAddr : BitVec 64) (addend : Int) : BitVec 64 :=
  if addend == 0 then symAddr else symAddr + BitVec.ofInt 64 addend

/-- `w` is an `ADRP Xd, #imm` (`1 immlo 10000 immhi Rd`). -/
def isAdrpWord (w : BitVec 32) : Bool := (w &&& 0x9f000000#32) == 0x90000000#32

/-- `w` is a 64-bit `ADD Xd, Xn, #imm12` with no shift (`1 0 0 100010 0 imm12 Rn Rd`). -/
def isAddImm64Word (w : BitVec 32) : Bool := (w &&& 0xffc00000#32) == 0x91000000#32

/-- `w` is an unconditional branch `B #imm` (`000101 imm26`). -/
def isBWord (w : BitVec 32) : Bool := (w &&& 0xfc000000#32) == 0x14000000#32

/-- The `ADR Xd, #0` template with destination register `rd` (`0 00 10000 0...0 Rd`). -/
def adrTemplate (rd : BitVec 32) : BitVec 32 := 0x10000000#32 ||| (rd &&& 0x1f#32)

/-! ## Code blocks -/

/-- One library's text, as a rigid block of relocatable code:
    - `code`: the bytes of the library's `.text*` input sections, concatenated in link order with
      alignment padding, *before* relocation (relocated fields hold the assembler's values);
    - `align`: the alignment the linker gives the block (its largest input-section alignment);
    - `symbols`: the functions it defines and their byte offsets in `code`;
    - `relocs`: its code relocations (`RelocEntry.off` is a byte offset in `code`); a relocation
      whose symbol is in `symbols` targets `base + off`, any other symbol resolves through `ρ`;
    - `externs`: functions it calls but does not define;
    - `weakRefs`: the subset of `externs` that the objects reference as undefined `STB_WEAK`
      symbols (a linker may leave these undefined, see `Placement.undefWeak`). -/
structure CodeBlock where
  code : List (BitVec 8)
  align : Nat := 4
  symbols : List (String × Nat) := []
  relocs : List RelocEntry := []
  externs : List String := []
  weakRefs : List String := []
  deriving Inhabited

/-- A library: its text block, its data objects, and the functions it exports (whose
    `.symtab` entries a linked binary must keep). -/
structure PlacedLib where
  name : String
  text : CodeBlock
  data : List SymDataInfo := []
  exports : List String := []
  deriving Inhabited

/-- Where a linker placed a library: text at `base`, every other symbol at `ρ sym`, which
    relaxable pairs/sites (by byte offset in the block) it relaxed, and which branches (by byte
    offset) it retargeted past a block `B` (branch-to-branch).

    The symbol map `ρ sym` gives:
    - the symbol's virtual address for direct code/data relocations, relaxed GOT (`GotToNopAdr` /
      `GotToAdrpAdd`) sites, data objects (`PlacedLib.data`), and extern stubs;
    - the GOT-slot virtual address for unrelaxed GOT (`adrGotPage` / `ld64GotLo12Nc`) and
      unrelaxed initial-exec TLS (`tlsieAdrGottprelPage21` / `tlsieLd64GottprelLo12Nc`) sites; and
    - the thread-pointer (`TPIDR_EL0`) offset for relaxed initial-exec TLS (`TLSIE` → `MOVZ`/`MOVK`),
      `TLSDESC` → `TLSLE`, and direct local-exec TLS (`TLSLE`) sites.
    `undefWeak sym` says the linker left the weak reference `sym` (one of the block's `weakRefs`)
    undefined: a direct `call26`/`jump26` to it is then patched to branch to the next instruction
    (AAELF64 §5.7.11.2, as `ld.lld -static` does), while its GOT sites still load the GOT slot at
    `ρ sym` (which then holds `0`).
    (Mixed relaxed+unrelaxed GOT accesses to the same symbol, GOT-loading a `PlacedLib.data`
    symbol, or a direct branch to a *defined* weak symbol that is also GOT-loaded unrelaxed, would
    require a separate GOT-slot map if ever needed.) -/
structure Placement where
  base : BitVec 64
  ρ : String → BitVec 64
  relax : Nat → Bool := fun _ => false
  b2b : Nat → Bool := fun _ => false
  undefWeak : String → Bool := fun _ => false

namespace CodeBlock

/-- Address of `sym` under placement `pl`: `base + off` for a block symbol, else `pl.ρ sym`. -/
def resolve (blk : CodeBlock) (pl : Placement) (sym : String) : BitVec 64 :=
  match lookup sym blk.symbols with
  | some off => pl.base + BitVec.ofNat 64 off
  | none => pl.ρ sym

/-- The relocation at byte offset `off`, if any (the first one; `Placeable` requires uniqueness). -/
def relocAt? (blk : CodeBlock) (off : Nat) : Option RelocEntry :=
  blk.relocs.find? (·.off == off)

/-- Relocation target `sym + addend` under `pl`. -/
def target (blk : CodeBlock) (pl : Placement) (r : RelocEntry) : BitVec 64 :=
  addSignedAddr (blk.resolve pl r.sym) r.addend

/-- The unrelocated 32-bit word at byte offset `off`. -/
def wordAt (blk : CodeBlock) (off : Nat) : BitVec 32 := wordOfBytesLE blk.code off

/-- The words at `off` and `off + 4` form an `ADRP Xd, sym` + `ADD Xd, Xd, :lo12:sym` pair that
    a linker may relax to `NOP` + `ADR Xd, sym` (`R_AARCH64_ADR_PREL_PG_HI21` and
    `R_AARCH64_ADD_ABS_LO12_NC` with the same symbol and addend, 64-bit unshifted `ADD`, and the
    same general-purpose register `Xd != 31` as `ADRP` destination, `ADD` source and `ADD`
    destination, since register 31 encodes `SP` in `ADD` but `XZR` in `ADR`). -/
def relaxableAt (blk : CodeBlock) (off : Nat) : Bool :=
  match blk.relocAt? off, blk.relocAt? (off + 4) with
  | some r1, some r2 =>
    r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.sym == r2.sym && r1.addend == r2.addend &&
    isAdrpWord (blk.wordAt off) && isAddImm64Word (blk.wordAt (off + 4)) &&
    (blk.wordAt off &&& 0x1f#32) == (blk.wordAt (off + 4) &&& 0x1f#32) &&
    ((blk.wordAt (off + 4) >>> 5) &&& 0x1f#32) == (blk.wordAt off &&& 0x1f#32) &&
    (blk.wordAt off &&& 0x1f#32) != 0x1f#32
  | _, _ => false

/-- The words at `off` and `off + 4` form a GOT-load `ADRP Xd, :got:sym` +
    `LDR Xd, [Xd, :got_lo12:sym]` pair (`R_AARCH64_ADR_GOT_PAGE` and
    `R_AARCH64_LD64_GOT_LO12_NC` with the same symbol, addend `0`, 64-bit unsigned `LDR`, and the
    same general-purpose register `Xd != 31` as `ADRP` destination, `LDR` base and `LDR`
    destination, matching `lld/ELF/Arch/AArch64.cpp` `tryRelaxAdrpLdr`). A linker may relax the
    pair to `NOP` + `ADR Xd, sym` (`pl.relax off = true, pl.relax (off + 4) = false`), to
    `ADRP Xd, sym` + `ADD Xd, Xd, :lo12:sym` (`pl.relax off = false, pl.relax (off + 4) = true`),
    or leave it as an unrelaxed GOT load (`pl.relax off = false, pl.relax (off + 4) = false`). -/
def gotPairAt (blk : CodeBlock) (off : Nat) : Bool :=
  match blk.relocAt? off, blk.relocAt? (off + 4) with
  | some r1, some r2 =>
    r1.kind == .adrGotPage && r2.kind == .ld64GotLo12Nc &&
    r1.sym == r2.sym && r1.addend == 0 && r2.addend == 0 &&
    isAdrpWord (blk.wordAt off) && isLdr64UnsignedWord (blk.wordAt (off + 4)) &&
    (blk.wordAt off &&& 0x1f#32) == (blk.wordAt (off + 4) &&& 0x1f#32) &&
    ((blk.wordAt (off + 4) >>> 5) &&& 0x1f#32) == (blk.wordAt off &&& 0x1f#32) &&
    (blk.wordAt off &&& 0x1f#32) != 0x1f#32
  | _, _ => false

/-- The word at `off` has an initial-exec TLS relocation (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21`
    on `ADRP Xd` or `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC` on `LDR Xd, [Xd, ...]`) that a static
    executable linker may relax to local-exec `MOVZ Xd, #:tprel_g1:sym, LSL #16` or
    `MOVK Xd, #:tprel_g0_nc:sym` when `pl.relax off = true`. Requires `Rn == Rt` on the `LDR`
    (matching standard compiler codegen; `lld/ELF/Arch/AArch64.cpp` `relaxTlsIeToLe` relaxes
    regardless of `Rn`, so `Rn != Rt` safely stays unrelaxed; `Rd = 31` is `XZR` in `ADRP`,
    `LDR`, `MOVZ`, and `MOVK`). -/
def tlsieRelaxableAt (blk : CodeBlock) (off : Nat) : Bool :=
  match blk.relocAt? off with
  | some r =>
    let w := blk.wordAt off
    match r.kind with
    | .tlsieAdrGottprelPage21 => isAdrpWord w
    | .tlsieLd64GottprelLo12Nc =>
      isLdr64UnsignedWord w && ((w >>> 5) &&& 0x1f#32) == (w &&& 0x1f#32)
    | _ => false
  | none => false

/-- Relocated word for a relaxed GOT or initial-exec TLS relocation site. -/
def patchGotOrTlsIeRelaxed (w : BitVec 32) (place target : BitVec 64)
    (kind : RelocKind) : BitVec 32 :=
  match kind with
  | .adrGotPage => nopWord
  | .ld64GotLo12Nc => lo12Word 0 (ldrToAddWord w) target
  | .tlsieAdrGottprelPage21 => tlsieMovzWord w target
  | .tlsieLd64GottprelLo12Nc => tlsieMovkWord w target
  | _ => patchRelocWord kind w place target

/-- Branch-to-branch candidate: branch relocation `r` (`call26`/`jump26`) targets a block word
    that is an unconditional `B` with a `jump26` relocation `r2`; a linker may then retarget the
    branch to `r2`'s target (`BL f` where `f: B g` becomes `BL g`, same behaviour). -/
def b2bNext? (blk : CodeBlock) (r : RelocEntry) : Option RelocEntry :=
  if r.kind == .call26 || r.kind == .jump26 then
    match lookup r.sym blk.symbols with
    | some symOff =>
      let t : Int := (symOff : Int) + r.addend
      if 0 ≤ t then
        match blk.relocAt? t.toNat with
        | some r2 => if r2.kind == .jump26 && isBWord (blk.wordAt t.toNat) then some r2 else none
        | none => none
      else none
    | none => none
  else none

/-- Target of relocation `r` at byte offset `off` under `pl`: `r2`'s target if `pl.b2b off` and
    `r` is a branch-to-branch candidate (`b2bNext? r = some r2`), else `blk.target pl r`. -/
def relocTarget (blk : CodeBlock) (pl : Placement) (off : Nat) (r : RelocEntry) : BitVec 64 :=
  match (if pl.b2b off then blk.b2bNext? r else none) with
  | some r2 => blk.target pl r2
  | none => blk.target pl r

/-- Relocation `r` is a direct branch (`call26`/`jump26`) to a weak reference of the block
    (`weakRefs`) that `pl` leaves undefined (`pl.undefWeak`); the linker then patches it to branch
    to the next instruction instead of to `relocTarget` (AAELF64 §5.7.11.2). -/
def undefWeakBranch (blk : CodeBlock) (pl : Placement) (r : RelocEntry) : Bool :=
  blk.weakRefs.contains r.sym && (r.kind == .call26 || r.kind == .jump26) && pl.undefWeak r.sym

/-- The pair at `off` is relaxed under `pl`. -/
def relaxedAt (blk : CodeBlock) (pl : Placement) (off : Nat) : Bool :=
  blk.relaxableAt off && pl.relax off

/-- The relocated word at byte offset `off` under placement `pl`:
    - the `ADRP` of a relaxed `ADRP`+`ADD` pair becomes `NOP`, its `ADD` becomes
      `ADR Xd, sym + addend`;
    - a GOT pair (`gotPairAt`) or initial-exec TLS relocation (`tlsieRelaxableAt`) is relaxed
      according to `pl.relax` (`GotToNopAdr`, `GotToAdrpAdd`, or `TlsIeToLe`);
    - any other relocated word is patched by `patchRelocWord` at `place = base + off`, targeting
      `place + 4` for a direct branch to an undefined weak reference (`undefWeakBranch`) and
      `relocTarget` (which applies branch-to-branch) otherwise;
    - unrelocated words are unchanged. -/
def patchedWord (blk : CodeBlock) (pl : Placement) (off : Nat) : BitVec 32 :=
  let w := blk.wordAt off
  match blk.relocAt? off with
  | none => w
  | some r =>
    let place := pl.base + BitVec.ofNat 64 off
    if blk.relaxedAt pl off then nopWord
    else if 4 ≤ off && blk.relaxedAt pl (off - 4) then
      adrWord (adrTemplate w) place (blk.target pl r)
    else if r.kind.isGotOrTlsIe && 4 ≤ off &&
        (blk.gotPairAt (off - 4) && pl.relax (off - 4)) then
      adrWord (adrTemplate w) place (blk.target pl r)
    else if r.kind.isGotOrTlsIe &&
        (blk.gotPairAt off || blk.tlsieRelaxableAt off ||
          (4 ≤ off && blk.gotPairAt (off - 4))) && pl.relax off then
      patchGotOrTlsIeRelaxed w place (blk.target pl r) r.kind
    else patchRelocWord r.kind w place
      (if blk.undefWeakBranch pl r then place + 4 else blk.relocTarget pl off r)

/-- The relocated bytes of the block under placement `pl`. -/
def patched (blk : CodeBlock) (pl : Placement) : List (BitVec 8) :=
  (List.range (blk.code.length / 4)).flatMap fun j =>
    bytesOfWordLE (blk.patchedWord pl (4 * j))

/-- Range and alignment condition for relocation `kind` at byte offset `off` (`place = base + off`)
    targeting `target` in `blk` under placement `pl`:
    - for `.adrGotPage`: `True` when relaxed to `NOP + ADR` (`gotPairAt off && pl.relax off`),
      or `AdrpInRange place target` otherwise;
    - for `.ld64GotLo12Nc`: `AdrInRange place target` when relaxed to `NOP + ADR`
      (`4 ≤ off && gotPairAt (off - 4) && pl.relax (off - 4)`), `True` when relaxed to
      `ADRP + ADD` (`4 ≤ off && gotPairAt (off - 4) && pl.relax off`), or `Lo12Aligned 3 target`
      when unrelaxed;
    - for `.tlsieAdrGottprelPage21` / `.tlsieLd64GottprelLo12Nc`: `TlsIeInRange target` when
      relaxed to local-exec (`tlsieRelaxableAt off && pl.relax off`), or `CodeRelocInRange kind`
      (`AdrpInRange` / `Lo12Aligned 3`) when unrelaxed;
    - for all other relocation kinds: `CodeRelocInRange kind place target`. -/
def relocInRange (blk : CodeBlock) (pl : Placement) (kind : RelocKind) (off : Nat)
    (place target : BitVec 64) : Prop :=
  match kind with
  | .adrGotPage =>
    if blk.gotPairAt off && pl.relax off then True
    else AdrpInRange place target
  | .ld64GotLo12Nc =>
    if 4 ≤ off && blk.gotPairAt (off - 4) && pl.relax (off - 4) then
      AdrInRange place target
    else if 4 ≤ off && blk.gotPairAt (off - 4) && pl.relax off then True
    else Lo12Aligned 3 target
  | .tlsieAdrGottprelPage21 =>
    if blk.tlsieRelaxableAt off && pl.relax off then TlsIeInRange target
    else AdrpInRange place target
  | .tlsieLd64GottprelLo12Nc =>
    if blk.tlsieRelaxableAt off && pl.relax off then TlsIeInRange target
    else Lo12Aligned 3 target
  | _ => CodeRelocInRange kind place target

/-- A linker placing the block under `pl` applies every relocation without overflow:
    - `base` is aligned to `align` (a positive multiple of 4), the block does not wrap, and its
      length is a multiple of 4;
    - relocations are at distinct, 4-aligned, in-bounds offsets and are code relocations
      (not `abs64`/`abs32`) whose targets (`relocTarget`) satisfy `relocInRange` (also for an
      `undefWeakBranch` site, which is conservative: the linker does not range-check it);
    - each relaxed pair's `ADR` (at `base + off + 4`) reaches its target (`AdrInRange`);
    - block symbols are 4-aligned and in bounds, distinct from externs, and every extern
      resolves outside the block. -/
structure Placeable (blk : CodeBlock) (pl : Placement) : Prop where
  align_pos : 0 < blk.align ∧ blk.align % 4 = 0
  base_aligned : pl.base.toNat % blk.align = 0
  no_wrap : pl.base.toNat + blk.code.length ≤ 2 ^ 64
  len_aligned : blk.code.length % 4 = 0
  relocs_nodup : (blk.relocs.map (·.off)).Nodup
  relocs_ok : ∀ r ∈ blk.relocs,
    r.off % 4 = 0 ∧ r.off + 4 ≤ blk.code.length ∧
    blk.relocInRange pl r.kind r.off (pl.base + BitVec.ofNat 64 r.off) (blk.relocTarget pl r.off r)
  relaxed_ok : ∀ off r, blk.relaxedAt pl off = true → blk.relocAt? (off + 4) = some r →
    AdrInRange (pl.base + BitVec.ofNat 64 (off + 4)) (blk.target pl r)
  symbols_ok : ∀ s ∈ blk.symbols, s.2 % 4 = 0 ∧ s.2 ≤ blk.code.length
  externs_ok : ∀ e ∈ blk.externs, lookup e blk.symbols = none ∧
    blk.code.length ≤ (pl.ρ e - pl.base).toNat

end CodeBlock

/-! ## Data objects -/

/-- Apply data relocation `r` (`abs64`, `abs32`, `prel32`; others leave `bytes` unchanged) to
    the bytes `bytes` of a data object placed at `addr`. -/
def PlacedLib.patchDataReloc (lib : PlacedLib) (pl : Placement) (addr : BitVec 64)
    (bytes : List (BitVec 8)) (r : RelocEntry) : List (BitVec 8) :=
  let t := addSignedAddr (lib.text.resolve pl r.sym) r.addend
  let put (n : Nat) (v : BitVec 64) := bytes.take r.off ++ bytesLE n v ++ bytes.drop (r.off + n)
  match r.kind with
  | .abs64 => put 8 t
  | .abs32 => put 4 t
  | .prel32 => put 4 (t - (addr + BitVec.ofNat 64 r.off))
  | _ => bytes

/-- The initial bytes of data object `d` under `pl`: its relocated bytes followed by
    `d.zeroTail` zero bytes, at address `pl.ρ d.sym`. -/
def PlacedLib.patchedData (lib : PlacedLib) (pl : Placement) (d : SymDataInfo) :
    List (BitVec 8) :=
  d.relocs.foldl (lib.patchDataReloc pl (pl.ρ d.sym)) d.bytes ++ List.replicate d.zeroTail 0#8

/-- Width in bytes of a data relocation (`0` for non-data kinds). -/
def dataRelocWidth : RelocKind → Nat
  | .abs64 => 8
  | .abs32 | .prel32 => 4
  | _ => 0

/-- A linker placing the library under `pl` applies every relocation without overflow:
    the text block is `Placeable`, data object symbols are distinct and not block symbols, each data object
    is aligned at `pl.ρ d.sym` without wrapping, and each data relocation is an in-bounds,
    in-range `abs64`/`abs32`/`prel32`. -/
structure PlacedLib.Placeable (lib : PlacedLib) (pl : Placement) : Prop where
  text : lib.text.Placeable pl
  data_nodup : (lib.data.map (·.sym)).Nodup
  data_ok : ∀ d ∈ lib.data,
    lookup d.sym lib.text.symbols = none ∧ 0 < d.align ∧ (pl.ρ d.sym).toNat % d.align = 0 ∧
    (pl.ρ d.sym).toNat + d.bytes.length + d.zeroTail ≤ 2 ^ 64
  data_relocs_ok : ∀ d ∈ lib.data, ∀ r ∈ d.relocs,
    0 < dataRelocWidth r.kind ∧ r.off + dataRelocWidth r.kind ≤ d.bytes.length ∧
    (r.kind = .abs32 → Abs32InRange (addSignedAddr (lib.text.resolve pl r.sym) r.addend)) ∧
    (r.kind = .prel32 → Prel32InRange (pl.ρ d.sym + BitVec.ofNat 64 r.off)
      (addSignedAddr (lib.text.resolve pl r.sym) r.addend))

/-! ## The placed program -/

/-- The library placed under `pl` as a `Program`: the patched text at `pl.base`, its symbols,
    a hook entry point for each extern `e` at `pl.ρ e` (consulted via `externs`), and override
    hooks `overrides` for its own functions. -/
def PlacedLib.program (lib : PlacedLib) (pl : Placement)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) : Program :=
  { base := pl.base
    code := lib.text.patched pl
    symbols := lib.text.symbols
    stubs := lib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)
    externs := externs
    overrides := overrides
    svc := svc }

/-- Runtime address of block symbol `name` under `pl` (`pl.base` if `name` is not a block symbol). -/
def PlacedLib.fnAddr (lib : PlacedLib) (pl : Placement) (name : String) : BitVec 64 :=
  pl.base + BitVec.ofNat 64 ((lookup name lib.text.symbols).getD 0)

/-! ## Multi-block placed libraries -/

/-- A library as several independently placed code blocks, its data objects, and the symbols
    it exports to callers. `exportSyms` maps an export (named as in `blocks`' `symbols`, e.g. a
    demangled Rust path) to its raw `.symtab` name in the objects (e.g. the mangled symbol) when
    the two differ (`elfSym`). -/
structure MultiPlacedLib where
  name : String
  blocks : List CodeBlock
  data : List SymDataInfo := []
  exports : List String := []
  exportSyms : List (String × String) := []
  deriving Inhabited

/-- The raw `.symtab` name of export `e` of `lib`: its `exportSyms` entry, or `e` itself. -/
def MultiPlacedLib.elfSym (lib : MultiPlacedLib) (e : String) : String :=
  (lookup e lib.exportSyms).getD e

/-- Linker-chosen parameters for placing a `MultiPlacedLib`:
    - `base i`: runtime start address of block `i` (`blocks[i]`);
    - `ρ sym`: runtime address of any symbol `sym` outside `blocks` (data objects and externs);
    - `relax i off`: whether the `ADRP`+`ADD` pair at byte `off` of block `i` was relaxed to
      `NOP`+`ADR`;
    - `b2b i off`: whether the unconditional branch (`b26`/`call26`) at byte `off` of block `i`,
      targeting an unconditional `B` (`b26`) in block `i`, was retargeted to that `B`'s target;
    - `undefWeak sym`: whether the weak reference `sym` was left undefined
      (`Placement.undefWeak`). -/
structure MultiPlacement where
  base : Nat → BitVec 64
  ρ : String → BitVec 64
  relax : Nat → Nat → Bool := fun _ _ => false
  b2b : Nat → Nat → Bool := fun _ _ => false
  undefWeak : String → Bool := fun _ => false

/-- First `(blockIdx, off)` pair for symbol `name` across `blocks`, searching from `startIdx`. -/
def lookupBlockSymAux (name : String) : Nat → List CodeBlock → Option (Nat × Nat)
  | _, [] => none
  | idx, blk :: rest =>
    match lookup name blk.symbols with
    | some off => some (idx, off)
    | none => lookupBlockSymAux name (idx + 1) rest

/-- First `(blockIdx, off)` pair for symbol `name` across `blocks`. -/
def lookupBlockSym (name : String) (blocks : List CodeBlock) : Option (Nat × Nat) :=
  lookupBlockSymAux name 0 blocks

/-- Runtime address of symbol `sym` under multi-block placement `mpl`: `mpl.base i + off` if `sym`
    is at offset `off` in block `i`, otherwise `mpl.ρ sym`. -/
def MultiPlacedLib.resolve (lib : MultiPlacedLib) (mpl : MultiPlacement) (sym : String) :
    BitVec 64 :=
  match lookupBlockSym sym lib.blocks with
  | some (i, off) => mpl.base i + BitVec.ofNat 64 off
  | none => mpl.ρ sym

/-- Projected single-block `Placement` for block `i` of `lib` under `mpl`: placed at `mpl.base i`,
    with all other blocks' symbols and external/data symbols resolved through `lib.resolve mpl`. -/
def MultiPlacedLib.blockPlacement (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat) :
    Placement :=
  { base := mpl.base i
    ρ := lib.resolve mpl
    relax := mpl.relax i
    b2b := mpl.b2b i
    undefWeak := mpl.undefWeak }

/-- Block `i` of `lib` viewed as a single-block `PlacedLib` sharing `lib.data` and `lib.exports`. -/
def MultiPlacedLib.blockLib (lib : MultiPlacedLib) (i : Nat) : PlacedLib :=
  { name := lib.name
    text := lib.blocks.getD i { code := [] }
    data := lib.data
    exports := lib.exports }

/-- Apply data relocation `r` (`abs64`, `abs32`, `prel32`; others leave `bytes` unchanged) to
    the bytes `bytes` of a data object placed at `addr` under `mpl`. -/
def MultiPlacedLib.patchDataReloc (lib : MultiPlacedLib) (mpl : MultiPlacement) (addr : BitVec 64)
    (bytes : List (BitVec 8)) (r : RelocEntry) : List (BitVec 8) :=
  let t := addSignedAddr (lib.resolve mpl r.sym) r.addend
  let put (n : Nat) (v : BitVec 64) := bytes.take r.off ++ bytesLE n v ++ bytes.drop (r.off + n)
  match r.kind with
  | .abs64 => put 8 t
  | .abs32 => put 4 t
  | .prel32 => put 4 (t - (addr + BitVec.ofNat 64 r.off))
  | _ => bytes

/-- The initial bytes of data object `d` under `mpl`: its relocated bytes followed by
    `d.zeroTail` zero bytes, at address `mpl.ρ d.sym`. -/
def MultiPlacedLib.patchedData (lib : MultiPlacedLib) (mpl : MultiPlacement) (d : SymDataInfo) :
    List (BitVec 8) :=
  d.relocs.foldl (lib.patchDataReloc mpl (mpl.ρ d.sym)) d.bytes ++ List.replicate d.zeroTail 0#8

/-- Two half-open address ranges `[b1, b1 + n1)` and `[b2, b2 + n2)` in `Nat` do not overlap. -/
def RangesDisjoint (b1 n1 b2 n2 : Nat) : Prop :=
  b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1

/-- A linker placing the multi-block library under `mpl` applies every relocation without overflow:
    - every block `i` is `Placeable` under its projected `lib.blockPlacement mpl i`;
    - distinct blocks occupy disjoint address ranges;
    - symbol names across all blocks are distinct (`symbols_nodup`);
    - data object symbols are distinct, not block symbols, aligned at `mpl.ρ d.sym` without
      wrapping, and each data relocation is an in-bounds, in-range `abs64`/`abs32`/`prel32`. -/
structure MultiPlacedLib.Placeable (lib : MultiPlacedLib) (mpl : MultiPlacement) : Prop where
  blocks_ok : ∀ (i : Nat) (hi : i < lib.blocks.length),
    lib.blocks[i].Placeable (lib.blockPlacement mpl i)
  blocks_disjoint : ∀ (i j : Nat) (hi : i < lib.blocks.length) (hj : j < lib.blocks.length),
    i < j → RangesDisjoint (mpl.base i).toNat lib.blocks[i].code.length
      (mpl.base j).toNat lib.blocks[j].code.length
  symbols_nodup : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup
  data_nodup : (lib.data.map (·.sym)).Nodup
  data_ok : ∀ d ∈ lib.data,
    lookupBlockSym d.sym lib.blocks = none ∧ 0 < d.align ∧ (mpl.ρ d.sym).toNat % d.align = 0 ∧
    (mpl.ρ d.sym).toNat + d.bytes.length + d.zeroTail ≤ 2 ^ 64
  data_relocs_ok : ∀ d ∈ lib.data, ∀ r ∈ d.relocs,
    0 < dataRelocWidth r.kind ∧ r.off + dataRelocWidth r.kind ≤ d.bytes.length ∧
    (r.kind = .abs32 → Abs32InRange (addSignedAddr (lib.resolve mpl r.sym) r.addend)) ∧
    (r.kind = .prel32 → Prel32InRange (mpl.ρ d.sym + BitVec.ofNat 64 r.off)
      (addSignedAddr (lib.resolve mpl r.sym) r.addend))

/-- Block `i` of `lib` placed under `mpl` as a `Program`. -/
def MultiPlacedLib.blockProgram (lib : MultiPlacedLib) (mpl : MultiPlacement) (i : Nat)
    (externs : String → Option (State → State) := fun _ => none)
    (overrides : String → Option (State → State) := fun _ => none)
    (svc : State → State := Syscall.standard) : Program :=
  (lib.blockLib i).program (lib.blockPlacement mpl i) externs overrides svc

/-- Runtime address of block symbol `name` under `mpl` (`mpl.base 0` if `name` is not a block
    symbol). -/
def MultiPlacedLib.fnAddr (lib : MultiPlacedLib) (mpl : MultiPlacement) (name : String) :
    BitVec 64 :=
  match lookupBlockSym name lib.blocks with
  | some (i, off) => mpl.base i + BitVec.ofNat 64 off
  | none => mpl.base 0

/-- Memory `m` holds `bytes` at `[addr, addr + bytes.length)`, byte `i` with permission
    `some (p (addr + i))` and not marked `lazyFree`. -/
def HoldsBytes (m : Memory) (addr : BitVec 64) (bytes : List (BitVec 8))
    (p : BitVec 64 → Perm) : Prop :=
  ∀ (i : Nat) (hi : i < bytes.length),
    m.read8 (addr + BitVec.ofNat 64 i) = bytes[i] ∧
    m.perm (addr + BitVec.ofNat 64 i) = some (p (addr + BitVec.ofNat 64 i)) ∧
    m.isLazyFree (addr + BitVec.ofNat 64 i) = false

/-- Every block of `lib` has its patched code loaded executable (`Perm.rx`) in memory `m`. -/
def MultiPlacedLib.CodeLoaded (lib : MultiPlacedLib) (mpl : MultiPlacement) (m : Memory) : Prop :=
  ∀ (i : Nat), i < lib.blocks.length → (lib.blockProgram mpl i).CodeLoaded m

end Arm64.Obj


