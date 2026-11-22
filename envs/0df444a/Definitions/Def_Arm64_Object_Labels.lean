-- Prove2me | Definitions.Def_Arm64_Object_Labels
-- name    : Arm64_Object_Labels
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:12:45.240072+00:00
-- url     : https://prove2.me/theorems/51a50286-2300-40a9-aaed-edf2205f3de6
-- title:
--   Arm64.Trusted.Object.Labels — Object-Level Label Provenance
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Object/Labels.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Labels.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Object/Labels.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Labels.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Object/Labels.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_Object_Placed

/-!
# Object-Level Label Provenance

Defines the pre-link relocatable object representation (`ExtractedObj`) emitted by
`trusted_extractor` and the declarative provenance relation `LabelsFromObjects`, which ties a
`MultiPlacedLib`'s unrelocated sections, `.bss` zero-tails, permissions, alignments, exported
entrypoints, `STT_OBJECT` symbols, external references, relocations, and `STB_WEAK` flags to
extracted `.o` symbol and relocation tables independently of the final binary's `.symtab`.
-/

@[expose] public section

namespace Arm64.Obj

/-- ELF symbol type (`ELF64_ST_TYPE`) in an extracted relocatable object. -/
inductive SymKind where
  | func | object | tls | section | other
  deriving DecidableEq, Repr, Inhabited

/-- ELF symbol binding (`ELF64_ST_BIND`) in an extracted relocatable object. -/
inductive SymBind where
  | local | global | weak | other
  deriving DecidableEq, Repr, Inhabited

/-- ELF symbol section index in an extracted relocatable object: `undef` (`SHN_UNDEF`), `sec idx`
    (allocated section `idx` of the object), or `other` (`SHN_ABS`, `SHN_COMMON`, or non-allocated). -/
inductive SymSec where
  | undef | sec (idx : Nat) | other
  deriving DecidableEq, Repr, Inhabited

/-- Non-no-op ELF relocation record in a raw section (`r_offset`, mapped `RelocKind` or `none` when
    the relocation code is outside `RelocKind`, `.symtab` index, signed `r_addend`). -/
structure RawReloc where
  off : Nat
  kind : Option RelocKind
  symIdx : Nat
  addend : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Allocated (`SHF_ALLOC`, non-`.eh_frame`) section of an extracted `.o` file, carrying its
    unrelocated byte payload (`[]` when `isNobits` is `true`) and raw relocation records. -/
structure RawSec where
  name : String
  bytes : List (BitVec 8)
  size : Nat
  align : Nat
  isExec : Bool
  readOnly : Bool
  isNobits : Bool
  isTls : Bool := false
  relocs : List RawReloc := []
  deriving DecidableEq, Repr, Inhabited

/-- One `.symtab` entry of an extracted `.o` file: `rawName` is the verbatim `.strtab` string and
    `name` is the extractor's demangled / disambiguated identifier. -/
structure RawSym where
  rawName : String
  name : String
  sec : SymSec
  value : Nat
  size : Nat
  kind : SymKind
  bind : SymBind
  deriving DecidableEq, Repr, Inhabited

/-- `SHT_GROUP` section group with flag `GRP_COMDAT` of an extracted `.o` file: `signature` is the
    `.strtab` name of the group's `sh_info` symbol and `members` are the indices (into
    `ExtractedObj.sections`) of its extracted member sections. -/
structure RawGroup where
  signature : String
  members : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Pre-link view of one relocatable `.o` file emitted directly by `trusted_extractor`, with its
    COMDAT groups in section header order. -/
structure ExtractedObj where
  name : String
  sections : List RawSec
  symbols : List RawSym
  groups : List RawGroup := []
  deriving DecidableEq, Repr, Inhabited

/-- Half-open byte slice `[start, start + len)` of `objs[oi].sections[si]`. -/
structure SliceOrigin where
  oi : Nat
  si : Nat
  start : Nat
  len : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `lld` drops section `si` of `objs[oi]`: it is a member of a COMDAT group whose signature an
    earlier group (in an earlier object, or earlier in the same object) already claimed. -/
def Discarded (objs : List ExtractedObj) (oi si : Nat) : Prop :=
  ∃ (o : ExtractedObj) (g : RawGroup) (gi : Nat),
    objs[oi]? = some o ∧ o.groups[gi]? = some g ∧ si ∈ g.members ∧
    ∃ (oj : Nat) (o' : ExtractedObj) (g' : RawGroup) (gj : Nat),
      objs[oj]? = some o' ∧ o'.groups[gj]? = some g' ∧
      g'.signature = g.signature ∧ (oj < oi ∨ (oj = oi ∧ gj < gi))

/-- Static `lld` resolution of non-local name `raw`, with `objs` in link (parse) order: `sy` at
    `(oi, k)` is an `STB_GLOBAL` / `STB_WEAK` definition in allocated, non-`Discarded` section
    `si`, and every other non-local definition of `raw` is an `STB_WEAK` definition in an allocated
    section that `sy` beats (`sy` is `STB_GLOBAL`, or the first weak definition). Two `STB_GLOBAL`
    definitions, any `SHN_ABS` / `SHN_COMMON` / `STB_GNU_UNIQUE` competitor, and a `Discarded`
    winner fail closed. -/
def Resolves (objs : List ExtractedObj) (raw : String) (oi k si : Nat) (sy : RawSym) : Prop :=
  raw ≠ "" ∧
  (∃ o, objs[oi]? = some o ∧ o.symbols[k]? = some sy) ∧
  sy.rawName = raw ∧ (sy.bind = .global ∨ sy.bind = .weak) ∧ sy.sec = .sec si ∧
  ¬Discarded objs oi si ∧
  ∀ oj k' o' sy', objs[oj]? = some o' → o'.symbols[k']? = some sy' →
    sy'.rawName = raw → sy'.bind ≠ .local → sy'.sec ≠ .undef → (oj ≠ oi ∨ k' ≠ k) →
    sy'.bind = .weak ∧ (∃ sj, sy'.sec = .sec sj) ∧
      (sy.bind = .global ∨ oi < oj ∨ (oi = oj ∧ k < k'))

/-- `sym` is either `base` or `base` qualified with defining object `objName` (`"base [objName]"`). -/
def SymNameDerived (sym base objName : String) : Prop :=
  sym = base ∨ sym = base ++ " [" ++ objName ++ "]"

/-- `sym` does not collide with any named `.symtab` entry (`rawName` or `SymNameDerived`) in `objs`,
    preventing synthetic labels on unnamed slices from spoofing real symbols. -/
def UnclaimedSymName (objs : List ExtractedObj) (sym : String) : Prop :=
  ∀ o ∈ objs, ∀ sy ∈ o.symbols, sy.rawName ≠ "" →
    sym ≠ sy.rawName ∧ ¬SymNameDerived sym sy.name o.name

/-- `sy` is a named `STT_OBJECT` symbol covering `[o.start, o.start + o.len)` in `o.si`. -/
def CoversDataSlice (o : SliceOrigin) (sy : RawSym) : Prop :=
  sy.kind = .object ∧ sy.sec = .sec o.si ∧
  sy.value = o.start ∧ sy.size = o.len ∧ sy.rawName ≠ ""

/-- Block `b` is the exact unrelocated executable byte slice `o` of `objs`, with aligned bounds and
    symbols either backed by `STT_FUNC` entries in `o` or unclaimed synthetic labels. -/
def ValidTextSlice (objs : List ExtractedObj) (b : CodeBlock) (o : SliceOrigin) : Prop :=
  ∃ obj sec, objs[o.oi]? = some obj ∧ obj.sections[o.si]? = some sec ∧ ¬Discarded objs o.oi o.si ∧
    sec.isExec = true ∧ sec.readOnly = true ∧ sec.isNobits = false ∧ sec.isTls = false ∧
    0 < o.len ∧ o.start % 4 = 0 ∧ o.len % 4 = 0 ∧ o.start + o.len ≤ sec.size ∧
    sec.bytes.length = sec.size ∧ b.code = (sec.bytes.drop o.start).take o.len ∧
    0 < sec.align ∧ b.align % Nat.gcd sec.align o.start = 0 ∧
    ∀ sym off, (sym, off) ∈ b.symbols →
      off < o.len ∧ off % 4 = 0 ∧
      ((∃ sy ∈ obj.symbols, sy.kind = .func ∧ sy.sec = .sec o.si ∧ sy.rawName ≠ "" ∧
          sy.value = o.start + off ∧ SymNameDerived sym sy.name obj.name) ∨
        UnclaimedSymName objs sym)

/-- Data entry `d` is the exact unrelocated non-executable slice `o` of `objs` (zero-filled of size
    `o.len` for `SHT_NOBITS`), with matching `readOnly`, alignment, and covering `STT_OBJECT` names,
    and with uncovered slices restricted to `UnclaimedSymName`. -/
def ValidDataSlice (objs : List ExtractedObj) (d : SymDataInfo) (o : SliceOrigin) : Prop :=
  ∃ obj sec, objs[o.oi]? = some obj ∧ obj.sections[o.si]? = some sec ∧ ¬Discarded objs o.oi o.si ∧
    sec.isExec = false ∧ sec.isTls = false ∧ o.start + o.len ≤ sec.size ∧
    d.readOnly = sec.readOnly ∧
    (if sec.isNobits then d.bytes = [] ∧ d.zeroTail = o.len
     else sec.bytes.length = sec.size ∧
          d.bytes = (sec.bytes.drop o.start).take o.len ∧ d.zeroTail = 0) ∧
    0 < sec.align ∧ d.align % Nat.gcd sec.align o.start = 0 ∧
    ((∃ sy ∈ obj.symbols, CoversDataSlice o sy ∧ SymNameDerived d.sym sy.name obj.name) ∨
      ((¬∃ sy ∈ obj.symbols, CoversDataSlice o sy) ∧ UnclaimedSymName objs d.sym))

/-- Placed `RelocEntry` `r` in a slice starting at `sliceStart` of object `oi` faithfully represents
    raw relocation `rr`: a `STB_LOCAL` symbol targets its own (non-`Discarded`) definition, and a
    non-local one (defined in `objs[oi]` or not) targets its `Resolves` winner across `objs` or, when
    nothing defines it, stays an external `rawName`. Fails closed on `rr.kind = none`, `.other`
    definitions, unresolvable names, or out-of-slice internal targets. -/
def RelocMatches (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO : Fin lib.blocks.length → SliceOrigin) (dO : Fin lib.data.length → SliceOrigin)
    (oi sliceStart : Nat) (rr : RawReloc) (r : RelocEntry) : Prop :=
  r.off + sliceStart = rr.off ∧ rr.kind = some r.kind ∧
  ∃ o sy, objs[oi]? = some o ∧ o.symbols[rr.symIdx]? = some sy ∧
    ((∃ oj sj ojObj secT tSym t,
        ((sy.bind = .local ∧ oj = oi ∧ sy.sec = .sec sj ∧ ¬Discarded objs oi sj ∧
            tSym = sy ∧ t = (sy.value : Int) + rr.addend) ∨
         (sy.bind ≠ .local ∧ ∃ k, Resolves objs sy.rawName oj k sj tSym ∧
            t = (tSym.value : Int) + rr.addend)) ∧
        objs[oj]? = some ojObj ∧ ojObj.sections[sj]? = some secT ∧
        ((secT.isExec = true ∧ ∃ bj off, lookupBlockSym r.sym lib.blocks = some (bj, off) ∧
            ∃ h : bj < lib.blocks.length, (bO ⟨bj, h⟩).oi = oj ∧ (bO ⟨bj, h⟩).si = sj ∧
              0 ≤ (off : Int) + r.addend ∧ (off : Int) + r.addend ≤ ((bO ⟨bj, h⟩).len : Int) ∧
              ((bO ⟨bj, h⟩).start + off : Int) + r.addend = t) ∨
         (secT.isExec = false ∧ secT.isTls = false ∧ lookupBlockSym r.sym lib.blocks = none ∧
            ∃ dj : Fin lib.data.length, lib.data[dj].sym = r.sym ∧
              (dO dj).oi = oj ∧ (dO dj).si = sj ∧ 0 ≤ r.addend ∧ r.addend ≤ ((dO dj).len : Int) ∧
              ((dO dj).start : Int) + r.addend = t) ∨
         (secT.isExec = false ∧ secT.isTls = true ∧ lookupBlockSym r.sym lib.blocks = none ∧
            (∀ d ∈ lib.data, d.sym ≠ r.sym) ∧
            ∃ ts ∈ ojObj.symbols, ts.sec = .sec sj ∧ ts.kind = .tls ∧ ts.rawName ≠ "" ∧
              r.sym = ts.rawName ∧ (ts.value : Int) + r.addend = t))) ∨
     (sy.sec = .undef ∧ sy.rawName = r.sym ∧ r.sym ≠ "" ∧ r.addend = rr.addend ∧
        lookupBlockSym r.sym lib.blocks = none ∧ (∀ d ∈ lib.data, d.sym ≠ r.sym) ∧
        ∀ o' ∈ objs, ∀ sy' ∈ o'.symbols, sy'.rawName = r.sym → sy'.bind ≠ .local → sy'.sec = .undef))

/-- Relocations `rs` of slice `o` correspond 1-to-1 (via index bijection `perm`) to
    `objs[o.oi].sections[o.si]`'s relocations in `[o.start, o.start + o.len)`. -/
def SliceRelocsMatch (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO : Fin lib.blocks.length → SliceOrigin) (dO : Fin lib.data.length → SliceOrigin)
    (o : SliceOrigin) (rs : List RelocEntry) : Prop :=
  ∃ obj sec, objs[o.oi]? = some obj ∧ obj.sections[o.si]? = some sec ∧
    let raw := sec.relocs.filter fun rr => decide (o.start ≤ rr.off ∧ rr.off < o.start + o.len)
    ∃ perm : List Nat,
      perm.length = raw.length ∧ perm.Nodup ∧ rs.length = raw.length ∧
      ∀ (k : Nat) (hk : k < raw.length) (hp : k < perm.length),
        ∃ hr : perm[k] < rs.length,
          RelocMatches objs lib bO dO o.oi o.start raw[k] rs[perm[k]]

/-- `x` is referenced in `objs` only as undefined `STB_WEAK` and never defined as non-local
    (including `SHN_ABS`/`SHN_COMMON`) or in any allocated section. -/
def WeakOnlyUndef (objs : List ExtractedObj) (x : String) : Prop :=
  (∃ o ∈ objs, ∃ sy ∈ o.symbols, sy.sec = .undef ∧ sy.rawName = x ∧ sy.bind = .weak) ∧
  ∀ o ∈ objs, ∀ sy ∈ o.symbols, sy.rawName = x →
    (sy.sec = .undef → sy.bind = .weak) ∧ (sy.bind ≠ .local → sy.sec = .undef) ∧ ∀ si, sy.sec ≠ .sec si

/-- Declarative provenance tying `lib` to the pre-link objects `objs` via slice witnesses `bO`, `dO`:
    1. `blocks_valid` / `data_valid`: unrelocated bytes of non-`Discarded` sections, `.bss`
       zero-tails, permissions, alignments, and `STT_FUNC` / `STT_OBJECT` symbol names match `objs`;
    2. `blocks_disjoint` / `data_disjoint` / `names_nodup`: slices of the same `(oi, si)` are
       pairwise disjoint and block/data symbol names are injective and mutually disjoint;
    3. `block_relocs` / `data_relocs`: every raw relocation in every kept slice is accounted for
       1-to-1 with exact target slice/offset (of the `Resolves` winner, for non-local symbols) or
       verbatim undefined `.strtab` `rawName`;
    4. `exports_valid`: each export `e ∈ lib.exports` is the `Resolves` winner of `lib.elfSym e`
       across `objs`, an `STT_FUNC` with `sy.name = e`;
    5. `externs_valid`: each block's `externs` are exactly its non-block `call26`/`jump26` targets
       across `lib.blocks` (disjoint from block and data symbols), and `weakRefs` satisfy
       `WeakOnlyUndef`.

    `objs` lists the link inputs in `lld` parse order (an archive member at its extraction point).
    Out of scope by precondition: `-shared` / `-pie` symbol preemption, `-r`,
    `--allow-multiple-definition`, `--wrap`, `--defsym`, linker scripts, LTO, and `.so` inputs. -/
structure LabelsFromObjects (objs : List ExtractedObj) (lib : MultiPlacedLib)
    (bO : Fin lib.blocks.length → SliceOrigin) (dO : Fin lib.data.length → SliceOrigin) : Prop where
  blocks_valid : ∀ i : Fin lib.blocks.length, ValidTextSlice objs lib.blocks[i] (bO i)
  data_valid : ∀ i : Fin lib.data.length, ValidDataSlice objs lib.data[i] (dO i)
  blocks_disjoint : ∀ i j : Fin lib.blocks.length, i ≠ j →
    (bO i).oi = (bO j).oi → (bO i).si = (bO j).si →
    RangesDisjoint (bO i).start (bO i).len (bO j).start (bO j).len
  data_disjoint : ∀ i j : Fin lib.data.length, i ≠ j →
    (dO i).oi = (dO j).oi → (dO i).si = (dO j).si →
    RangesDisjoint (dO i).start (dO i).len (dO j).start (dO j).len
  names_nodup : ((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup ∧
    (lib.data.map (·.sym)).Nodup ∧
    ∀ d ∈ lib.data, lookupBlockSym d.sym lib.blocks = none
  block_relocs : ∀ i : Fin lib.blocks.length,
    SliceRelocsMatch objs lib bO dO (bO i) lib.blocks[i].relocs
  data_relocs : ∀ i : Fin lib.data.length,
    SliceRelocsMatch objs lib bO dO (dO i) lib.data[i].relocs
  exports_valid : ∀ e ∈ lib.exports, ∃ bi off,
    lookupBlockSym e lib.blocks = some (bi, off) ∧ ∃ h : bi < lib.blocks.length,
      ∃ k sy, Resolves objs (lib.elfSym e) (bO ⟨bi, h⟩).oi k (bO ⟨bi, h⟩).si sy ∧
        sy.kind = .func ∧ sy.name = e ∧ sy.value = (bO ⟨bi, h⟩).start + off
  externs_valid : ∀ b ∈ lib.blocks,
    (∀ r ∈ b.relocs, (r.kind = .call26 ∨ r.kind = .jump26) →
      lookupBlockSym r.sym lib.blocks = none → r.sym ∈ b.externs) ∧
    (∀ x ∈ b.externs, lookupBlockSym x lib.blocks = none ∧ (∀ d ∈ lib.data, d.sym ≠ x) ∧
      ∃ b' ∈ lib.blocks, ∃ r ∈ b'.relocs, (r.kind = .call26 ∨ r.kind = .jump26) ∧ r.sym = x) ∧
    (∀ w ∈ b.weakRefs, w ∈ b.externs ∧ WeakOnlyUndef objs w)

end Arm64.Obj


