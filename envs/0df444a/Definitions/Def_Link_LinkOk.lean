-- Prove2me | Definitions.Def_Link_LinkOk
-- name    : Link_LinkOk
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-25T09:56:06.723155+00:00
-- url     : https://prove2.me/theorems/32f019ed-67d0-5126-a954-b75fc1b690d0
-- title:
--   Link sanity for placed AArch64 libraries — one hook per extern address, no overlapping code, data or externs
-- statement:
--   A hypothesis for contracts of placed machine code (`Obj.PlacedLib` and `Obj.MultiPlacedLib`, bundle `Arm64_Object_Placed`), to be assumed beside `Placeable`. It is not from DeepMind: it is written for prove2.me.
--
--   **Why.** `Placeable` asks that every relocation of the code fits where the linker put it, and, for a multi-block library, that the code blocks are disjoint. It does not relate the addresses of external functions and data objects to each other or to the code. In the semantics, a branch to the address of an external function runs the hook of the first extern of the code block listed at that address, while a contract assumes a hook for each extern by its name. So when two externs share an address, the hook assumed for the second is never run. Two published statements were disproved through exactly this: `Poly1305Libsodium.internalOk_poly1305_finish` and `Poly1305Libsodium.internalOk_init_update_final_oneshot`.
--
--   **The definitions.** `InRange a b n` says the address $a$ is in the $n$ bytes from $b$. `dataSize d` is the size of data object $d$: its initial bytes and its zero tail. `HooksAgree fns ρ externs` says that two names in `fns` that $ρ$ places at one address have the same entry in the hook table `externs`. `DataDisjoint ds ρ` says the data objects `ds` pairwise do not overlap.
--
--   The external functions of a library (`PlacedLib.externFns`, `MultiPlacedLib.externFns`) are the externs of its code blocks that are not data objects of the library and, for a multi-block library, not symbols of one of its blocks: the code refers to those through relocations too, but they are not called through a hook.
--
--   `PlacedLib.LinkOk lib pl externs` and `MultiPlacedLib.LinkOk lib mpl externs` say:
--   - `HooksAgree` for the library's external functions: two of them at one address are one function, as with a symbol alias, and have one hook;
--   - no external function lies inside a code block or inside a data object;
--   - the data objects do not overlap each other or any code block.
--
--   A link of distinct functions and objects at distinct, non-overlapping addresses satisfies all of these for every hook table. Two different functions at one address are allowed only when their hooks agree.
-- source:
--   Google DeepMind, code-verification (arm64-semantics), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, consistency conditions on the placement of a PlacedLib or MultiPlacedLib (module Arm64/Trusted/Object/Placed.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Object/Placed.lean) that its Placeable does not impose: external functions at one address have one hook, lie outside the code and data, and data objects do not overlap; ours, not DeepMind's

import Definitions.Def_Arm64_Object_Placed

/-!
# Link sanity for placed AArch64 libraries

`Obj.PlacedLib.Placeable` and `Obj.MultiPlacedLib.Placeable` (bundle `Arm64_Object_Placed`) ask that
every relocation of the code fits, but not that the external functions and the data objects are
laid out consistently with each other. In the semantics, a branch to the address of an external
function runs the hook of the first extern listed at that address, while a contract assumes a hook
for each extern by name. `LinkOk` asks for the consistency a real link gives:

- two external functions at one address have the same hook (they are one function, for example
  through a symbol alias);
- no external function lies inside a code block or a data object;
- data objects do not overlap each other or a code block.

An extern of a code block that names a data object of the library (a reference to the data) is not
an external function; neither is, in a multi-block library, one that names a symbol of another block.
-/

namespace Link

open Arm64 Arm64.Obj

/-- The address `a` lies in the half-open range of `n` bytes from `b` (as natural numbers). -/
def InRange (a b : BitVec 64) (n : Nat) : Prop :=
  b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n

/-- The number of bytes data object `d` occupies: its initial bytes and its zero tail. -/
def dataSize (d : SymDataInfo) : Nat :=
  d.bytes.length + d.zeroTail

/-- Externs placed at one address by `ρ` have the same hook in `externs`. -/
def HooksAgree (fns : List String) (ρ : String → BitVec 64)
    (externs : String → Option (State → State)) : Prop :=
  ∀ e₁ ∈ fns, ∀ e₂ ∈ fns, ρ e₁ = ρ e₂ → externs e₁ = externs e₂

/-- The data objects `ds`, at the addresses `ρ` gives their symbols, pairwise do not overlap. -/
def DataDisjoint (ds : List SymDataInfo) (ρ : String → BitVec 64) : Prop :=
  ds.Pairwise fun d₁ d₂ =>
    RangesDisjoint (ρ d₁.sym).toNat (dataSize d₁) (ρ d₂.sym).toNat (dataSize d₂)

/-! ## Single-block libraries -/

/-- The external functions of `lib`: the externs of its code block that are not data objects of
`lib`. -/
def PlacedLib.externFns (lib : PlacedLib) : List String :=
  lib.text.externs.filter fun e => (lib.data.map (·.sym)).all (· ≠ e)

/-- `lib` placed by `pl`, with the hooks `externs`, is laid out as a real link lays it out:
`HooksAgree` for its external functions; no external function in the code block or a data object;
data objects disjoint from each other and from the code block. -/
def PlacedLib.LinkOk (lib : PlacedLib) (pl : Placement)
    (externs : String → Option (State → State)) : Prop :=
  HooksAgree (PlacedLib.externFns lib) pl.ρ externs ∧
  (∀ e ∈ (PlacedLib.externFns lib), ¬ InRange (pl.ρ e) pl.base lib.text.code.length) ∧
  (∀ e ∈ (PlacedLib.externFns lib), ∀ d ∈ lib.data, ¬ InRange (pl.ρ e) (pl.ρ d.sym) (dataSize d)) ∧
  DataDisjoint lib.data pl.ρ ∧
  (∀ d ∈ lib.data,
    RangesDisjoint pl.base.toNat lib.text.code.length (pl.ρ d.sym).toNat (dataSize d))

/-! ## Multi-block libraries -/

/-- The external functions of `lib`: the externs of its code blocks that are neither symbols of a
block nor data objects of `lib`. -/
def MultiPlacedLib.externFns (lib : MultiPlacedLib) : List String :=
  (lib.blocks.flatMap (·.externs)).filter fun e =>
    (lookupBlockSym e lib.blocks).isNone && (lib.data.map (·.sym)).all (· ≠ e)

/-- `lib` placed by `mpl`, with the hooks `externs`, is laid out as a real link lays it out:
`HooksAgree` for its external functions; no external function in a code block or a data object;
data objects disjoint from each other and from every code block. -/
def MultiPlacedLib.LinkOk (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (externs : String → Option (State → State)) : Prop :=
  HooksAgree (MultiPlacedLib.externFns lib) mpl.ρ externs ∧
  (∀ e ∈ (MultiPlacedLib.externFns lib), ∀ (i : Nat) (hi : i < lib.blocks.length),
    ¬ InRange (mpl.ρ e) (mpl.base i) lib.blocks[i].code.length) ∧
  (∀ e ∈ (MultiPlacedLib.externFns lib), ∀ d ∈ lib.data, ¬ InRange (mpl.ρ e) (mpl.ρ d.sym) (dataSize d)) ∧
  DataDisjoint lib.data mpl.ρ ∧
  (∀ d ∈ lib.data, ∀ (i : Nat) (hi : i < lib.blocks.length),
    RangesDisjoint (mpl.base i).toNat lib.blocks[i].code.length (mpl.ρ d.sym).toNat (dataSize d))

end Link


