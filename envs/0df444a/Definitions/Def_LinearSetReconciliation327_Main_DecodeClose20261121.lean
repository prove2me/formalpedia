-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_DecodeClose20261121
-- name    : LinearSetReconciliation327_Main_DecodeClose20261121
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:04:37.767536+00:00
-- url     : https://prove2.me/theorems/ae71374b-5266-4783-91b5-9545ea02f02a
-- title:
--   The decoder's payload model: `wordsOf`, `HoldsVecPad`, `packMem`, `testBit`
-- statement:
--   This bundle publishes the memory vocabulary the CR decoder and the unpack block share: the word count $\mathrm{wordsOf}\;W\;M$ of a packed $M$-bit payload in $W$-bit words, the predicate `HoldsVecPad` saying that the $m$-word block at a base holds the packed payload of a binary vector, the packing function `packMem`, and the read-back lemma `testBit_packMem` saying that bit $b$ of word $j$ of the packed payload is the $b$-th coordinate of row $j$.  Together with $\mathrm{wordsOf}\;W\;(W m) = m$ this is what makes a bit-by-bit scan of the payload provably enumerate the support of the vector.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), \u00a72.3; the decoder's memory model.

/-
# `_65_dec_close` 鈥?the `hSk` calling convention propagated through the decoder's six stage contracts

This bundle closes gap (4) of the Theorem 6.5 decoder report.  `Solutions/_65_repair_hSk.lean`
(stage `res`) and `Solutions/_65_repair_block.lean` (the six-field structure) are *not* importable
from a `Definitions` bundle, so this file carries their 搂1-搂8 verbatim (`_65_repair_hSk`, which is
itself `_65_repair_block` 搂1-搂7 with the `hSk` conjunct added, plus its 搂8 non-vacuity), and then
proves what was missing:

* `DstZero`, `dstZero_word`, `dstZero_iff`, `dstZero_writeArray`, `dstZero_asmCopy` 鈥?the calling
  convention as a state predicate, its pointwise form, and the fact that a write to a block disjoint
  from the CR payload preserves it (this is what makes the assembly stage compatible with it);
* `ColOutAsZ` 鈥?the column stage's post / the assembly's pre, i.e. `ColOutAs` **plus** the conjunct;
* `TopDecStagesZ` 鈥?the six stage contracts with the conjunct propagated (`col` -> `as` -> `res`);
* `topDecCorrects_of_stagesZ`, `topDecCorrectsSeed_of_stagesZ` 鈥?the composition;
* 搂10 non-vacuity: a model of all six fields using the real `SassemP`/`SresP` and the real
  `stageRun_asP`/`stageRun_resP` (`stagesZ_model`), the composition at that model
  (`stagesZ_model_corrects`), and an inhabitant of the full `hSk` precondition at `M = 1` with
  `wordsOf 12 1 = 1`, i.e. where the zeroed block is a genuine word (`hSkPre_M1_inhabited`).

No `sorry`, no `admit`, no new axiom.  Imports: `Mathlib` and the published `Definitions` bundles.
-/

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec

/-!
# `_65_repair_hSk` — the repaired `Sres` contract, with the sketch's calling convention

This is §1-§7 of `Solutions/_65_repair_block.lean` (unchanged: `setVec`/`HoldsVec`/`HoldsVecPad`,
the XOR block, the XOR block's `Sem` spec, the repaired `Sres = SresP`, and the repaired `Sassem`,
`stageRun_asCore`/`stageRun_asP`), with **one** change:

`SresP`'s `Ssketch` **accumulates into** the destination block (`resDst E`): its loop XORs the
columns into the words `[resDst, resDst + wordsOf W M)` and the prologue does *not* zero them.  The
calling convention is therefore part of the sketch stage's precondition (see
`Solutions/_65_sketch_stmts.lean`, `stageRun_sketch`), and `stageRun_resCore`/`stageRun_resP` must
carry it:

  `writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem`

The conjunct is added to
* the **precondition of the `hSk` argument**, i.e. the exact contract the sketch stage must be
  instantiated at, and
* the theorem's **own precondition** `I`, since `stageRun_resCore` obtains the conjunct from its
  caller and passes it on to `hSk`.

Nothing else changes: the proofs of both theorems are the old ones (the `hSk` hypothesis is passed
through verbatim), so the modification is purely a contract strengthening.

§8 records the non-vacuity of the added conjunct.

This file is `sorry`-free and self-contained (`Mathlib` + the published `Definitions` bundle only).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace C8R

/-! ## 1. The payload vocabulary

Side B's `C8.setVec`/`Lists`/`OutListIs`/`HoldsVec`/`DecInputAt`, restated verbatim, plus the
repairs.  These are the *only* predicates the six stage fields mention. -/

/-- The `0/1` vector of a set of coordinates (Side B, verbatim). -/
def setVec (N : ℕ) (S : Finset ℕ) : Fin N → ZMod 2 := fun i => if (i : ℕ) ∈ S then 1 else 0

theorem setVec_eq_one {N : ℕ} {S : Finset ℕ} {i : Fin N} :
    setVec N S i = 1 ↔ (i : ℕ) ∈ S := by
  unfold setVec
  by_cases h : (i : ℕ) ∈ S <;> simp [h]

/-- A list is an enumeration of the set `S` (Side B, verbatim). -/
def Lists (L : List ℕ) (S : Finset ℕ) : Prop := L.Nodup ∧ ∀ v : ℕ, v ∈ L ↔ v ∈ S

/-- The state's explicit output list enumerates `S` (Side B, verbatim). -/
def OutListIs (s : RAMState) (S : Finset ℕ) : Prop := Lists (outList s) S

/-- The `ZMod 2`-support of a vector, as a `Finset ℕ`. -/
def supp {n : ℕ} (x : Fin n → ZMod 2) : Finset ℕ :=
  (univ.filter fun i => x i = 1).image fun i => i.val

theorem mem_supp {n : ℕ} (x : Fin n → ZMod 2) (v : ℕ) :
    v ∈ supp x ↔ ∃ i : Fin n, i.val = v ∧ x i = 1 := by
  unfold supp
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, hv, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hv, hx⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, hv⟩

/-- **The bridge**: "the decoder outputs the support of `x`" is exactly "its output list enumerates
`supp x`".  Side B's `outputsSupport_iff_outListIs`, verbatim. -/
theorem outputsSupport_iff_outListIs {n : ℕ} (s : RAMState) (x : Fin n → ZMod 2) :
    OutputsSupport s x ↔ OutListIs s (supp x) := by
  unfold OutputsSupport OutListIs Lists
  constructor
  · rintro ⟨hnd, hmem⟩
    exact ⟨hnd, fun v => (hmem v).trans (mem_supp x v).symm⟩
  · rintro ⟨hnd, hmem⟩
    exact ⟨hnd, fun v => (hmem v).trans (mem_supp x v)⟩

/-! ## 2. `HoldsVec` at the padded length

`_65_bridge_block` §5 established that Side A's `Sassem` transfers `d` words, which is the *padded*
row-major payload `W * d` bits, not Side B's packed `sch.N`-bit vector
(`packed_lt_padded_length`).  `_65_bridge_block` §6 established that Side B's `DecInputAt` pins *all*
of memory and is therefore contradictory with any frame.  The repair is therefore:

* the **estimate** buffer is `HoldsVecPad W m` — `m` words, i.e. the padded `W * m` bits;
* the **decoder's own** payload is `HoldsVec W M` at `M = CR.rows N t` (genuinely packed, `M` bits),
  stored by `DecInputOn` at its own base. -/

/-- Side B's `HoldsVec` (verbatim): the words `[base, base + wordsOf W M)` are the packed `M`-bit
vector `y`.  Kept for a *decoder's own* payload, whose length really is `M = CR.rows N t` bits. -/
def HoldsVec (W M : ℕ) (base : ℕ) (s : RAMState) (y : Fin M → ZMod 2) : Prop :=
  ∀ j : ℕ, j < wordsOf W M → s.mem (base + j) = packMem W y j

/-- **The repaired `HoldsVec`**: the length is the *padded* `W * m` bits, i.e. `m` words by
`asm_words_eq_padded`.  This is the payload `Sassem` moves (`m = det 0` words), and it is a
different payload from `HoldsVec W sch.N`, not a different length of the same one. -/
def HoldsVecPad (W m : ℕ) (base : ℕ) (s : RAMState) (y : Fin (W * m) → ZMod 2) : Prop :=
  ∀ j : ℕ, j < wordsOf W (W * m) → s.mem (base + j) = packMem W y j

/-- **The padded row-major payload of `m` row prefixes**: bit `W * j + b` is bit `b` of row `j`'s
prefix (zero on the padding).  `wordsOf W (W * m) = m`, so this is an `m`-word block. -/
def asmVec (W m : ℕ) (pref : Fin m → List (ZMod 2)) : Fin (W * m) → ZMod 2 :=
  fun p =>
    if h : p.val / W < m then
      (if (pref ⟨p.val / W, h⟩).getD (p.val % W) 0 = 1 then 1 else 0)
    else 0

/-- `m ≤ W * ceil(m/W)`: the padding only ever adds bits (copied from `Def_..._Top65`, which is not
importable here). -/
theorem le_mul_wordsOf (W : ℕ) (hW : 0 < W) (m : ℕ) : m ≤ W * wordsOf W m := by
  have h := Nat.div_add_mod (m + W - 1) W
  have hmod : (m + W - 1) % W ≤ W - 1 := by
    have := Nat.mod_lt (m + W - 1) hW
    omega
  unfold wordsOf
  omega

/-- `ceil(W * T / W) = T`: a word-aligned block of `T` words is exactly `T` words (copied from
`Def_..._Top65`). -/
theorem wordsOf_mul (W T : ℕ) (hW : 0 < W) : wordsOf W (W * T) = T := by
  unfold wordsOf
  have h1 : W * T + W - 1 = (W - 1) + T * W := by
    rw [Nat.mul_comm W T]; omega
  rw [h1, Nat.add_mul_div_right (W - 1) T hW, Nat.div_eq_of_lt (by omega), Nat.zero_add]

/-- **The padded assembly length is `m` words.**  `Sassem` transfers `d = sch.m` words, which is the
padded row-major payload `W * sch.m` bits. -/
theorem asm_words_eq_padded (W m : ℕ) (hW : 0 < W) : wordsOf W (W * m) = m :=
  wordsOf_mul W m hW

/-- The repaired `HoldsVec` really is an *`m`-word* statement. -/
theorem holdsVecPad_iff_words {W m : ℕ} (hW : 0 < W) {base : ℕ} {s : RAMState}
    {y : Fin (W * m) → ZMod 2} :
    HoldsVecPad W m base s y ↔ ∀ j : ℕ, j < m → s.mem (base + j) = packMem W y j := by
  unfold HoldsVecPad
  rw [asm_words_eq_padded W m hW]

/-- The packed length really is different: if `W * m < n` then the packed vector needs strictly more
words than the padded row-major block.  In the row-column regime `m` may be polylogarithmic while
`n / W` is linear-over-logarithmic, so keeping `sch.N` blows 6.5's time budget. -/
theorem packed_lt_padded_length {W n m : ℕ} (hW : 0 < W) (hmn : W * m < n) :
    wordsOf W (W * m) < wordsOf W n := by
  rw [wordsOf_mul W m hW]
  unfold wordsOf
  exact (Nat.lt_div_iff_mul_lt hW).mpr (by
    have h1 : m * W = W * m := Nat.mul_comm m W
    omega)

/-! ## 3. `DecInputOn`: the positional repair of `DecInputAt`

`DecInputAt W M y Jl s` conjoins three things: *all* of memory is `hintMem W y Jl`, and the three
registers `r0 = 0`, `r1 = wordsOf W M`, `r2 = Jl.length`.  Its first conjunct pins memory far beyond
the payload, which is what made Side B's `res`/`cr` fields (whose postcondition conjoins a frame
`HoldsVec ... x̂` at another base) unsatisfiable.

`DecInputOn W M β y Jl s` is the positional version: the payload sits at the word base `β`, the
register discipline is `r0 = β`, `r1 = wordsOf W M`, `r2 = Jl.length`, and **only** the window
`[β, β + wordsOf W M + Jl.length)` is pinned.  At `β = 0` it is exactly `DecInputAt` minus the
"rest of memory is zero" conjunct (`decInputAt_iff`). -/

/-- **The repaired `DecInputAt`.** -/
def DecInputOn (W M : ℕ) (β : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) (s : RAMState) : Prop :=
  (∀ j : ℕ, j < wordsOf W M + Jl.length → s.mem (β + j) = hintMem W y Jl j) ∧
    s.regs 0 = β ∧ s.regs 1 = wordsOf W M ∧ s.regs 2 = Jl.length

/-- Side B's `DecInputAt` (verbatim), for the comparison. -/
def DecInputAt (W M : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) (s : RAMState) : Prop :=
  (∀ j : ℕ, s.mem j = hintMem W y Jl j) ∧ s.regs 0 = 0 ∧ s.regs 1 = wordsOf W M ∧
    s.regs 2 = Jl.length

/-- **The content a downstream decoder reads** (the conjunct of Side B's `cr` field that is *not* a
frame): inside its window, `DecInputOn` presents the packed syndrome vector.  This is exactly
`HoldsVec W M β` at the decoder's own base. -/
theorem decInputOn_holdsVec {W M β : ℕ} {y : Fin M → ZMod 2} {Jl : List ℕ} {s : RAMState}
    (h : DecInputOn W M β y Jl s) : HoldsVec W M β s y := by
  intro j hj
  obtain ⟨hmem, -, -, -⟩ := h
  rw [hmem j (by omega), hintMem, if_pos hj]

/-- **The content, unpacked**: the payload words and the three registers. -/
theorem decInputOn_payload {W M β : ℕ} {y : Fin M → ZMod 2} {Jl : List ℕ} {s : RAMState}
    (h : DecInputOn W M β y Jl s) :
    (∀ j : ℕ, j < wordsOf W M → s.mem (β + j) = packMem W y j) ∧ s.regs 0 = β ∧
      s.regs 1 = wordsOf W M ∧ s.regs 2 = Jl.length :=
  ⟨decInputOn_holdsVec h, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **Inhabitant 1**: `decoderStart` satisfies `DecInputOn` at `β = 0`.  So the repaired predicate is
not vacuous, and every `decoderStart`-shaped layout is a model of it. -/
theorem decInputOn_decoderStart (W M : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) :
    DecInputOn W M 0 y Jl (decoderStart W y Jl) := by
  refine ⟨fun j _ => ?_, ?_, ?_, ?_⟩ <;> simp [decoderStart, initState]

/-- `DecInputAt` implies `DecInputOn` at `β = 0`: the repair is a weakening. -/
theorem decInputOn_of_decInputAt {W M : ℕ} {y : Fin M → ZMod 2} {Jl : List ℕ} {s : RAMState}
    (h : DecInputAt W M y Jl s) : DecInputOn W M 0 y Jl s := by
  obtain ⟨hmem, h0, h1, h2⟩ := h
  exact ⟨fun j _ => by simpa using hmem j, by simpa using h0, h1, h2⟩

/-- `List.getD` is `0` past the end. -/
theorem getD_zero_of_length_le : ∀ (l : List ℕ) (n : ℕ), l.length ≤ n → l.getD n 0 = 0
  | [], n, _ => rfl
  | a :: t, 0, h => by simp at h
  | a :: t, n + 1, h => by
      rw [List.getD_cons_succ]
      exact getD_zero_of_length_le t n (by simp at h; omega)

/-- **What `DecInputAt` additionally demands**: all of memory past the decoder's own window is zero.
This is the conjunct that made Side B's `res`/`cr` fields unsatisfiable. -/
theorem decInputAt_forces_zero {W M : ℕ} {y : Fin M → ZMod 2} {Jl : List ℕ} {s : RAMState}
    (h : DecInputAt W M y Jl s) : ∀ a : ℕ, wordsOf W M + Jl.length ≤ a → s.mem a = 0 := by
  intro a ha
  obtain ⟨hmem, -, -, -⟩ := h
  rw [hmem a]
  unfold hintMem
  rw [if_neg (by omega)]
  exact getD_zero_of_length_le Jl (a - wordsOf W M) (by omega)

/-- **`DecInputAt` is `DecInputOn` at `β = 0` plus "the rest of memory is zero"** — the exact
characterisation of the repair. -/
theorem decInputAt_iff (W M : ℕ) (y : Fin M → ZMod 2) (Jl : List ℕ) (s : RAMState) :
    DecInputAt W M y Jl s ↔
      DecInputOn W M 0 y Jl s ∧ ∀ a : ℕ, wordsOf W M + Jl.length ≤ a → s.mem a = 0 := by
  constructor
  · intro h
    exact ⟨decInputOn_of_decInputAt h, decInputAt_forces_zero h⟩
  · rintro ⟨h1, h0⟩
    obtain ⟨hmem, hr0, hr1, hr2⟩ := h1
    refine ⟨fun a => ?_, by simpa using hr0, hr1, hr2⟩
    by_cases ha : a < wordsOf W M + Jl.length
    · simpa using hmem a ha
    · rw [h0 a (by omega)]
      unfold hintMem
      rw [if_neg (by omega)]
      exact (getD_zero_of_length_le Jl (a - wordsOf W M) (by omega)).symm

/-- `DecInputOn` only constrains its own window: any state that agrees with it there (and on the
three registers) satisfies it too.  This is the frame property the repair buys. -/
theorem decInputOn_of_agree {W M β : ℕ} {y : Fin M → ZMod 2} {Jl : List ℕ} {s s' : RAMState}
    (h : DecInputOn W M β y Jl s)
    (hmem : ∀ j : ℕ, j < wordsOf W M + Jl.length → s'.mem (β + j) = s.mem (β + j))
    (hr0 : s'.regs 0 = s.regs 0) (hr1 : s'.regs 1 = s.regs 1) (hr2 : s'.regs 2 = s.regs 2) :
    DecInputOn W M β y Jl s' := by
  obtain ⟨hm, h0, h1, h2⟩ := h
  exact ⟨fun j hj => by rw [hmem j hj, hm j hj], by rw [hr0, h0], by rw [hr1, h1],
    by rw [hr2, h2]⟩

/-- **Inhabitant 2 (the point of the repair): `DecInputOn` and a frame at another base are
simultaneously satisfiable.**  Given *any* memory function whose words at `[base, base + m)` are the
packed vector `x`, and a payload base `β` disjoint from that range, there is a state satisfying the
whole `res`/`cr` precondition: the decoder's window and the `x̂` frame together.  The old
`DecInputAt` forbids this (`not_decInputAt_and_holdsVec`). -/
theorem decInputOn_sat_with_frame {W M m β base : ℕ} (hW : 0 < W) {y : Fin M → ZMod 2}
    {Jl : List ℕ} {x : Fin (W * m) → ZMod 2} {mem : ℕ → ℕ}
    (hmem : ∀ j : ℕ, j < m → mem (base + j) = packMem W x j)
    (hdisj : β + (wordsOf W M + Jl.length) ≤ base) :
    ∃ s' : RAMState, DecInputOn W M β y Jl s' ∧ HoldsVecPad W m base s' x := by
  classical
  refine ⟨⟨β, fun i => if i = 0 then β else if i = 1 then wordsOf W M else
      if i = 2 then Jl.length else 0,
      fun a => if a < β + (wordsOf W M + Jl.length) then hintMem W y Jl (a - β) else mem a⟩,
    ⟨fun j hj => ?_, by simp, by simp, by simp⟩, ?_⟩
  · simp only
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
  · rw [holdsVecPad_iff_words hW]
    intro j hj
    simp only
    rw [if_neg (by omega)]
    exact hmem j hj

/-- The packed vector is nonzero on the word of any set coordinate. -/
theorem packMem_setVec_pos {W N : ℕ} (hW : 0 < W) {S : Finset ℕ} {p : Fin N}
    (hp : (p : ℕ) ∈ S) : 0 < packMem W (setVec N S) ((p : ℕ) / W) := by
  unfold packMem
  have hnonneg : ∀ q ∈ (univ : Finset (Fin N)),
      0 ≤ (if q.val / W = p.val / W ∧ setVec N S q = 1 then 2 ^ (q.val % W) else 0) := by
    intro q _
    split_ifs <;> positivity
  have hle := Finset.single_le_sum (s := (univ : Finset (Fin N)))
    (f := fun q : Fin N =>
      if q.val / W = p.val / W ∧ setVec N S q = 1 then 2 ^ (q.val % W) else 0)
    hnonneg (Finset.mem_univ p)
  have hpv : (if p.val / W = p.val / W ∧ setVec N S p = 1 then 2 ^ (p.val % W) else 0) =
      2 ^ (p.val % W) := by
    rw [if_pos]
    exact ⟨rfl, by simp [setVec, hp]⟩
  rw [hpv] at hle
  exact lt_of_lt_of_le (by positivity) hle

/-- **The defect, restated with this block's vocabulary**: Side B's `res`/`cr` fields conjoin
`DecInputAt` with a nonempty frame at a base past the payload, and no state satisfies both. -/
theorem not_decInputAt_and_holdsVec {W M N base : ℕ} (hW : 0 < W)
    {y : Fin M → ZMod 2} {S : Finset ℕ} {s : RAMState}
    (hbase : wordsOf W M ≤ base) (hS : ∃ p : Fin N, (p : ℕ) ∈ S) :
    ¬ (DecInputAt W M y [] s ∧ HoldsVec W N base s (setVec N S)) := by
  rintro ⟨hdec, hmem⟩
  obtain ⟨p, hp⟩ := hS
  have hWpos : p.val < W * wordsOf W N :=
    lt_of_lt_of_le p.isLt (le_mul_wordsOf W hW N)
  have hWpos' : p.val < wordsOf W N * W := by rw [Nat.mul_comm]; exact hWpos
  have hword : p.val / W < wordsOf W N := (Nat.div_lt_iff_lt_mul hW).mpr hWpos'
  have h1 : s.mem (base + p.val / W) = packMem W (setVec N S) (p.val / W) := hmem _ hword
  have hble : wordsOf W M ≤ base + p.val / W :=
    le_trans hbase (Nat.le_add_right base (p.val / W))
  have h2 : s.mem (base + p.val / W) = 0 := decInputAt_forces_zero hdec _ (by simpa using hble)
  have hpos := packMem_setVec_pos hW hp
  rw [h2] at h1
  omega

/-- **The same conjunction with `DecInputOn` is inhabited** — the formal statement of the repair.
This is the `res`/`cr` field shape with the repaired predicate: it has a model. -/
theorem decInputOn_and_holdsVecPad_sat {W M N m β base : ℕ} (hW : 0 < W)
    {y : Fin M → ZMod 2} {S : Finset ℕ} {x : Fin (W * m) → ZMod 2} {mem : ℕ → ℕ}
    (hx : ∀ j : ℕ, j < m → mem (base + j) = packMem W x j)
    (hdisj : β + wordsOf W M ≤ base) :
    ∃ s' : RAMState, DecInputOn W M β y [] s' ∧ HoldsVecPad W m base s' x :=
  decInputOn_sat_with_frame hW hx (by simpa using hdisj)

/-! ## 4. The register convention: the epilogue

Side A's word copy leaves `r0 = r1 = L` and `r2 = dst` (`copyState` at `j = L`), where `L` is the
number of words moved — *not* `DecInputAt`'s `(0, wordsOf W M, 0)`.  The bridge round showed this to
be defect 1: the register triple alone makes `DecInputAt` unreachable from a copy.  The three
instructions below restore `DecInputOn`'s triple, and cost `3`. -/

/-- The epilogue of the residual stage: `r0 := 0`, `r1 := wordsOf W M`, `r2 := 0`. -/
def epilogue (W M : ℕ) : List Instr := [iImm r0 0, iImm r1 (wordsOf W M), iImm r2 0]

theorem epilogue_noBranch (W M : ℕ) : NoBranch (epilogue W M) := by
  simp [epilogue, NoBranch, Instr.NoBranchI]

theorem epilogue_length (W M : ℕ) : (epilogue W M).length = 3 := rfl

/-- **The epilogue establishes `DecInputOn`'s registers** from any register file, and does not touch
memory.  It is the bridge from the register convention a word copy leaves (`r0 = r1 = L`, `r2 = dst`)
to the decoder's convention `(0, wordsOf W M, 0)`. -/
theorem runBlock_epilogue {M : ℕ} {E : RAMEnv} (hW : 1 < 2 ^ E.W)
    (hM : wordsOf E.W M < 2 ^ E.W) (s : RAMState) :
    (runBlock (epilogue E.W M) E s).regs 0 = 0 ∧
      (runBlock (epilogue E.W M) E s).regs 1 = wordsOf E.W M ∧
      (runBlock (epilogue E.W M) E s).regs 2 = 0 ∧
      (runBlock (epilogue E.W M) E s).mem = s.mem ∧
      (runBlock (epilogue E.W M) E s).pc = s.pc + 3 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hM' : wordsOf E.W M % 2 ^ E.W = wordsOf E.W M := Nat.mod_eq_of_lt hM
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [epilogue, runBlock_cons, runBlock_nil, execInstr, h1, hM']

/-! ## 5. `xorStmt`: the word-wise symmetric difference

The residual payload is `a + CR x̂` where `a` is the stored syndrome and `CR x̂` is recomputed by the
sketch subroutine.  On the packed representation the sum is a **word-wise XOR**: `packMem` is a
packing of bits, so `packMem W (u + z) j = packMem W u j ^^^ packMem W z j` (`RP.packMem_add`,
the word-XOR machinery of `Def_..._HintUpdateRoot20261120`, carried locally because that bundle is
not importable here).

`xorStmt` is `copyStmt` with the store replaced by a load XOR store: twelve instructions of body,
`15` instructions of code, `15 L + 2` steps of run.  Its spec `xorArray_spec` mirrors
`copyArray_spec` (`Def_..._DecoderLemmas`) line for line. -/

/-! ### 5.0 The packing algebra

`packMem` is a sum of distinct powers of two, so the binary digits of a word are exactly its
bits: the packing of a pointwise sum is the XOR of the packings.  Carried locally from
`Def_..._HintUpdateRoot20261120` (not importable here). -/

namespace RP

/-- Little-endian packing of the bits `f 0, …, f (W-1)` into one word. -/
def ofBits (W : ℕ) (f : ℕ → Bool) : ℕ := ∑ b ∈ Finset.range W, if f b then 2 ^ b else 0

theorem geom_two (W : ℕ) : (∑ b ∈ Finset.range W, 2 ^ b) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 0 < 2 ^ n := Nat.two_pow_pos n
      omega

theorem ofBits_lt (W : ℕ) (f : ℕ → Bool) : ofBits W f < 2 ^ W := by
  have h : ofBits W f ≤ ∑ b ∈ Finset.range W, 2 ^ b := by
    refine Finset.sum_le_sum ?_
    intro b _
    split_ifs with hb
    · exact le_rfl
    · exact Nat.zero_le _
  rw [geom_two] at h
  have h2 : 0 < 2 ^ W := Nat.two_pow_pos W
  omega

theorem ofBits_succ (W : ℕ) (f : ℕ → Bool) :
    ofBits (W + 1) f = (if f 0 then 1 else 0) + 2 * ofBits W (fun b => f (b + 1)) := by
  rw [ofBits, ofBits, Finset.sum_range_succ']
  have h2 : (∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ (k + 1) else 0))
      = 2 * ∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ k else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    split_ifs with hk
    · rw [pow_succ]
      ring
    · rfl
  rw [h2]
  by_cases h : f 0 = true
  · simp [h, Nat.add_comm]
  · simp [h, Nat.add_comm]

theorem ofBits_testBit (W : ℕ) (f : ℕ → Bool) (b : ℕ) (hb : b < W) :
    (ofBits W f).testBit b = f b := by
  induction W generalizing b f with
  | zero => omega
  | succ n ih =>
      rw [ofBits_succ]
      cases b with
      | zero =>
          rw [Nat.testBit_zero, Nat.add_mul_mod_self_left]
          by_cases h : f 0 = true <;> simp [h]
      | succ b =>
          rw [Nat.testBit_succ]
          have hdiv : ((if f 0 then 1 else 0) + 2 * ofBits n (fun b => f (b + 1))) / 2
              = ofBits n (fun b => f (b + 1)) := by
            rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
            by_cases h : f 0 = true <;> simp [h]
          rw [hdiv]
          exact ih (fun b => f (b + 1)) b (by omega)

theorem packMem_eq_ofBits (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a = ofBits W (fun b => decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1)) := by
  rw [packMem, ofBits]
  have hR : (∑ b ∈ Finset.range W,
        (if decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) then 2 ^ b else 0))
      = ∑ b ∈ (Finset.range W).filter
          (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1), 2 ^ b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b _
    by_cases h : ∃ p : Fin M, p.val = a * W + b ∧ y p = 1 <;> simp [h]
  rw [hR]
  have hL : (∑ p : Fin M, (if p.val / W = a ∧ y p = 1 then 2 ^ (p.val % W) else 0))
      = ∑ b ∈ (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
          (fun p => p.val % W), 2 ^ b := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
    · intro p hp p' hp' heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp hp'
      have heq' : p.val % W = p'.val % W := heq
      refine Fin.ext ?_
      rw [← Nat.div_add_mod p.val W, hp.1, ← Nat.div_add_mod p'.val W, hp'.1, heq']
  rw [hL]
  have himg : (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
        (fun p => p.val % W)
      = (Finset.range W).filter (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and,
      exists_prop]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨Nat.mod_lt _ hW, p, ?_, hp2⟩
      rw [← hp1, Nat.mul_comm]
      exact (Nat.div_add_mod p.val W).symm
    · rintro ⟨hb, p, hp, hp2⟩
      refine ⟨p, ⟨?_, hp2⟩, ?_⟩
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [himg]

theorem testBit_packMem (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a b : ℕ)
    (hb : b < W) :
    (packMem W y a).testBit b = decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_testBit W _ b hb

theorem packMem_lt (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a < 2 ^ W := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_lt W _

theorem decide_zmod2_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

theorem decide_row_add {M : ℕ} (q : ℕ) (u z : Fin M → ZMod 2) :
    decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1)
      = (decide (∃ p : Fin M, p.val = q ∧ u p = 1)
          ^^ decide (∃ p : Fin M, p.val = q ∧ z p = 1)) := by
  have hrow : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) → ∀ p' : Fin M,
      p'.val = q → y p' = 1 := by
    intro y hy p' hp'
    obtain ⟨p, hp, hpy⟩ := hy
    have : p' = p := Fin.ext (by rw [hp', hp])
    rwa [this]
  by_cases hex : ∃ p : Fin M, p.val = q
  · obtain ⟨p₀, hp₀⟩ := hex
    have e : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) ↔ y p₀ = 1 := by
      intro y
      exact ⟨fun hy => hrow y hy p₀ hp₀, fun hy => ⟨p₀, hp₀, hy⟩⟩
    have e1 : decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1) = decide ((u + z) p₀ = 1) := by
      by_cases h : (u + z) p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e (u + z)).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e (u + z)).mp hc))]
    have e2 : decide (∃ p : Fin M, p.val = q ∧ u p = 1) = decide (u p₀ = 1) := by
      by_cases h : u p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e u).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e u).mp hc))]
    have e3 : decide (∃ p : Fin M, p.val = q ∧ z p = 1) = decide (z p₀ = 1) := by
      by_cases h : z p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e z).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e z).mp hc))]
    rw [e1, e2, e3]
    show decide (u p₀ + z p₀ = 1) = (decide (u p₀ = 1) ^^ decide (z p₀ = 1))
    exact decide_zmod2_add _ _
  · have h1 : ¬ ∃ p : Fin M, p.val = q ∧ (u + z) p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h2 : ¬ ∃ p : Fin M, p.val = q ∧ u p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h3 : ¬ ∃ p : Fin M, p.val = q ∧ z p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
    rfl

/-- **`packMem` is additive**: word-wise XOR of the packed payloads is the packing of the pointwise
sum.  This is why the residual stage's XOR implements the symmetric difference. -/
theorem packMem_add (W : ℕ) (hW : 0 < W) {M : ℕ} (u z : Fin M → ZMod 2) (a : ℕ) :
    packMem W (u + z) a = packMem W u a ^^^ packMem W z a := by
  refine Nat.eq_of_testBit_eq ?_
  intro b
  by_cases hb : b < W
  · rw [testBit_packMem W hW _ a b hb, Nat.testBit_xor, testBit_packMem W hW _ a b hb,
      testBit_packMem W hW _ a b hb, decide_row_add]
  · have hbW : W ≤ b := by omega
    have h1 : packMem W (u + z) a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h2 : packMem W u a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h3 : packMem W z a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_xor, Nat.testBit_lt_two_pow h2,
      Nat.testBit_lt_two_pow h3]
    rfl

end RP

theorem mem_symmDiff {a : ℕ} {A B : Finset ℕ} :
    a ∈ symmDiff A B ↔ (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A) := by
  rw [symmDiff_def, Finset.sup_eq_union]
  simp only [Finset.mem_union, Finset.mem_sdiff]

/-- **`setVec` is additive over symmetric difference**: characteristic vectors of the symmetric
difference are the pointwise sum of the characteristic vectors (in characteristic two). -/
theorem setVec_symmDiff (N : ℕ) (A B : Finset ℕ) :
    setVec N (symmDiff A B) = setVec N A + setVec N B := by
  funext i
  have h := mem_symmDiff (a := (i : ℕ)) (A := A) (B := B)
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hA : (i : ℕ) ∈ A <;> by_cases hB : (i : ℕ) ∈ B
  · have hnot : (i : ℕ) ∉ symmDiff A B := by simp [h, hA, hB]
    simp [setVec, hA, hB, hnot, h11]
  · have hyes : (i : ℕ) ∈ symmDiff A B := by simp [h, hA, hB]
    simp [setVec, hA, hB, hyes]
  · have hyes : (i : ℕ) ∈ symmDiff A B := by simp [h, hA, hB]
    simp [setVec, hA, hB, hyes]
  · have hnot : (i : ℕ) ∉ symmDiff A B := by simp [h, hA, hB]
    simp [setVec, hA, hB, hnot]

/-- **The residual payload, word by word**: the packing of the symmetric difference of two sets is the
word-wise XOR of their packings.  This is the identity the residual stage's program computes. -/
theorem packMem_setVec_symmDiff {W M : ℕ} (hW : 0 < W) (A B : Finset ℕ) (j : ℕ) :
    packMem W (setVec M (symmDiff A B)) j =
      packMem W (setVec M A) j ^^^ packMem W (setVec M B) j := by
  conv_lhs => rw [setVec_symmDiff]
  exact RP.packMem_add W hW _ _ j

/-! ### 5.1 The machine state of the XOR loop -/

/-- The state of the XOR loop at counter `j`: the first `j` words of the destination have been
replaced by the XOR of the two arrays. -/
def xorState (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) : RAMState where
  pc := pc
  mem := writeArray dst m (fun i => m (dst + i) ^^^ m (src + i)) j
  regs := fun d =>
    if d = r0 then j else if d = r1 then L else if d = r2 then dst else
      if d = r3 then src else if d = r4 then 1 else if d = r10 then 0 else
        if d = r11 then 0 else if d = r12 then 0 else if d = r13 then 0 else
          if d = r15 then 0 else r d

/-- The loop test: `r0 < r1`, the counter below the length. -/
def xorCond : Cond := .lt r15 r0 r1

/-- The loop body: load, load, XOR, store, advance, clear the five scratch registers. -/
def xorBody : List Instr :=
  [iAdd r13 r3 r0, iLd r10 r13, iAdd r12 r2 r0, iLd r11 r12, iBxor r11 r11 r10, iSt r12 r11,
    iAdd r0 r0 r4, iImm r10 0, iImm r11 0, iImm r12 0, iImm r13 0, iImm r15 0]

/-- The word-wise XOR block. -/
def xorStmt : Stmt := .loop xorCond (.code xorBody)

lemma xorStmt_len : xorStmt.len = 15 := rfl

theorem xorBody_spec (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (j : ℕ) (hj : j < L) (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W)
    (hwordd : ∀ i < L, m (dst + i) < 2 ^ E.W) :
    runBlock xorBody E { runBlock xorCond.code E (xorState pc dst src L m r j) with pc := pc + 2 } =
      { xorState pc dst src L m r (j + 1) with pc := pc + 14 } := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hsj : (src + j) % 2 ^ E.W = src + j := Nat.mod_eq_of_lt (by omega)
  have hdj : (dst + j) % 2 ^ E.W = dst + j := Nat.mod_eq_of_lt (by omega)
  have hj1 : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have hm : writeArray dst m (fun i => m (dst + i) ^^^ m (src + i)) j (src + j) = m (src + j) :=
    writeArray_frame dst m _ j _ (by omega)
  have hmd : writeArray dst m (fun i => m (dst + i) ^^^ m (src + i)) j (dst + j) = m (dst + j) :=
    writeArray_frame dst m _ j _ (Or.inr (le_refl _))
  have hv : m (src + j) % 2 ^ E.W = m (src + j) := Nat.mod_eq_of_lt (hword j hj)
  have hvd : m (dst + j) % 2 ^ E.W = m (dst + j) := Nat.mod_eq_of_lt (hwordd j hj)
  have hxor : (m (dst + j) ^^^ m (src + j)) % 2 ^ E.W = m (dst + j) ^^^ m (src + j) :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (hwordd j hj) (hword j hj))
  apply ramState_eq_of
  · simp only [xorBody, Fin.isValue, Cond.code, xorCond, xorState, runBlock_cons, execInstr,
      ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, Nat.zero_mod, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff] <;> omega
  · simp only [xorBody, Fin.isValue, Cond.code, xorCond, xorState, runBlock_cons, execInstr,
      ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, hsj, hm, hv, hdj, hmd, hvd, hxor, Nat.zero_mod,
      writeArray]
  · intro d
    fin_cases d <;>
      simp only [xorBody, Fin.isValue, Cond.code, xorCond, xorState, runBlock_cons, execInstr,
        ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne, Function.update_self, hj1, Nat.zero_mod, Fin.zero_eta,
        Nat.add_left_cancel_iff, Fin.mk_one, Fin.reduceFinMk]

theorem xorCond_eval (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    xorCond.eval (xorState pc dst src L m r j) ↔ j < L := by
  simp [xorCond, Cond.eval, xorState]

theorem xorBodyIter (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) (hj : j < L)
    (hAt : At P pc (Stmt.compile xorStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W)
    (hwordd : ∀ i < L, m (dst + i) < 2 ^ E.W) :
    Sem P E (pc + xorCond.code.length + 1) pc
      { runBlock xorCond.code E (xorState pc dst src L m r j) with
        pc := pc + xorCond.code.length + 1 }
      (fun k s' => k = 13 ∧ s' = xorState pc dst src L m r (j + 1)) := by
  obtain ⟨_, _, hbody, hjmp⟩ := at_loop hAt
  have hbodyAt : At P (pc + 2) xorBody := hbody
  have hjmpAt : P[pc + 14]? = some (iJmp pc) := hjmp
  have hrun : Sem P E (pc + 2) (pc + 14)
      { runBlock xorCond.code E (xorState pc dst src L m r j) with pc := pc + 2 }
      (fun k s' => k = 12 ∧ s' = { xorState pc dst src L m r (j + 1) with pc := pc + 14 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) xorBody _ hbodyAt (by simp [xorBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact xorBody_spec E pc dst src L m r j hj hW hL hdst hsrc hdisj hword hwordd
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem xorCond_exit (E : RAMEnv) (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock xorCond.code E (xorState pc dst src L m r L) with pc := pc + 15 } : RAMState) =
      { xorState pc dst src L m r L with pc := pc + 15 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [xorCond, Cond.code, xorState, runBlock_cons, runBlock_nil, execInstr]

/-- **The XOR block's `Sem` spec** — `copyArray_spec` with the store replaced by a load XOR store.
From the loop head, in at most `15 L + 2` steps, the first `L` destination words are the XOR of the
two arrays, and the machine is at the address `compile` leaves after the loop. -/
theorem xorArray_spec (P : Program) (E : RAMEnv) (pc dst src L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (hAt : At P pc (Stmt.compile xorStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hdst : dst + L ≤ 2 ^ E.W) (hsrc : src + L ≤ 2 ^ E.W)
    (hdisj : src + L ≤ dst ∨ dst + L ≤ src)
    (hword : ∀ i < L, m (src + i) < 2 ^ E.W)
    (hwordd : ∀ i < L, m (dst + i) < 2 ^ E.W) :
    Sem P E pc (pc + 15) (xorState pc dst src L m r 0)
      (fun k s' => k ≤ 15 * L + 2 ∧ s' = { xorState pc dst src L m r L with pc := pc + 15 }) := by
  have h := Sem.loop P E pc xorCond (.code xorBody) hAt hW L
    (fun j => xorState pc dst src L m r j) (fun _ => 13)
    (fun _ => rfl)
    (fun j hj => (xorCond_eval pc dst src L m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((xorCond_eval pc dst src L m r L).mp hf))
    (fun j hj => xorBodyIter P E pc dst src L m r j hj hAt hW hL hdst hsrc hdisj hword hwordd)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (xorCond.code.length + 1 + 13)) = 15 * L := by
      change (∑ j ∈ Finset.range L, (15 : ℕ)) = 15 * L
      exact sum_range_const_mul L 15
    rw [hsum] at hcost
    change k ≤ 2 + 15 * L at hcost
    omega
  · rw [hs]
    exact xorCond_exit E pc dst src L m r

/-! ### 5.2 What the XOR leaves in memory -/

/-- The destination words after the XOR: `i < L` is the XOR, everything else is untouched. -/
theorem xorState_mem_get (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (i : ℕ) (hi : i < L) :
    (xorState pc dst src L m r L).mem (dst + i) = m (dst + i) ^^^ m (src + i) := by
  simp only [xorState]
  exact writeArray_get dst m (fun i => m (dst + i) ^^^ m (src + i)) L i hi

/-- The XOR leaves every address outside `[dst, dst + L)` alone. -/
theorem xorState_mem_frame (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (a : ℕ)
    (ha : a < dst ∨ dst + L ≤ a) : (xorState pc dst src L m r L).mem a = m a := by
  simp only [xorState]
  exact writeArray_frame dst m (fun i => m (dst + i) ^^^ m (src + i)) L a ha

/-- The registers the XOR loop leaves. -/
theorem xorState_regs_after (pc dst src L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    (xorState pc dst src L m r L).regs 0 = L ∧ (xorState pc dst src L m r L).regs 1 = L ∧
      (xorState pc dst src L m r L).regs 2 = dst := by
  simp [xorState]

/-! ## 6. The repaired `Sres`

Side B's `res` field asks for `DecInputAt` (payload at word `0`, `r0 = 0`, `r1 = wordsOf W M`,
`r2 = 0`) **and** the frame `HoldsVec ... x̂` — which `not_decInputAt_and_holdsVec` refutes.  Side A's
`Sres` is a bare word copy `resInit; copyStmt`, which (a) leaves `r0 = r1 = L`, `r2 = dst`, (b) only
*overwrites* the CR payload with the residual instead of forming `a + CR x̂`, and (c) has no `x̂`
frame.

The repair, with the shape the reconciliation round prescribed:

```
Sres = seq Ssketch (seq (.code resInit) (seq xorStmt (.code epilogue)))
```

* `Ssketch` — the CR sketch subroutine `x̂ ↦ CR x̂`, writing the packed syndrome into the CR payload.
  This is the one part of the residual stage whose program does not exist yet; it enters as the
  `StageRun` hypothesis `hSk` (see the residual list);
* `resInit` — Side A's twelve-instruction prologue, plus one `imm` clearing `r11` (the XOR's second
  scratch register), so `13` instructions;
* `xorStmt` — the word-wise XOR of the residual array into the CR payload (§5);
* `epilogue = [imm r0 0; imm r1 (wordsOf W M); imm r2 0]` — restores `DecInputOn`'s register triple.

## The contract

pre:  `HoldsVec E.W M (resSrc E) s (setVec M Aset)` (the stored syndrome `a = CR x`, packed at the
      residual array) **and** the frame `HoldsVecPad E.W m xhatBase s estVec` (the estimate `x̂`);
post: `DecInputOn E.W M 0 (setVec M (symmDiff Aset Bset)) [] s` — the residual payload at word `0`,
      with the *repaired* predicate — **and** the same frame.

so the frame survives the stage, which is what `Scr` needs and what `DecInputAt` forbade. -/

/-- `det` slot 7: the payload base of the `CR` call. -/
def hdrCrBase : ℕ := 7
/-- `det` slot 6: the base of the residual array. -/
def hdrResBase : ℕ := 6
/-- `det` slot 10: the number of words the residual stage moves. -/
def hdrWords : ℕ := 10

/-- The `CR` payload base. -/
def resDst (E : RAMEnv) : ℕ := E.det hdrCrBase % 2 ^ E.W
/-- The residual array base. -/
def resSrc (E : RAMEnv) : ℕ := E.det hdrResBase % 2 ^ E.W
/-- The number of words the residual stage moves. -/
def resLen (E : RAMEnv) : ℕ := E.det hdrWords % 2 ^ E.W

/-- `Sres`'s prologue: `r2 := CR payload base` (slot 7), `r3 := residual base` (slot 6), `r1 := words
to move` (slot 10), the loop scratch cleared — Side A's `resInit` plus the `r11` that `xorStmt`
uses. -/
def resInitX : List Instr :=
  [ iImm r15 hdrCrBase, iTbl r2 r15,
    iImm r15 hdrResBase, iTbl r3 r15,
    iImm r15 hdrWords, iTbl r1 r15,
    iImm r4 1, iImm r0 0, iImm r10 0, iImm r11 0, iImm r12 0, iImm r13 0, iImm r15 0 ]

lemma resInitX_noBranch : NoBranch resInitX := by
  simp [resInitX, NoBranch, Instr.NoBranchI]

lemma resInitX_length : resInitX.length = 13 := rfl

/-- A header slot index fits in a word as soon as `W ≥ 11`: `2 ^ 11 = 2048 > 11`. -/
lemma slot_lt {E : RAMEnv} (hW : 11 ≤ E.W) {k : ℕ} (hk : k ≤ 11) : k < 2 ^ E.W := by
  have h1 : (2 : ℕ) ^ 11 ≤ 2 ^ E.W := Nat.pow_le_pow_right (by norm_num) hW
  have h2 : k < 2 ^ 11 := by norm_num; omega
  omega

/-- After the prologue the machine is in the XOR loop's head state. -/
theorem runBlock_resInitX {E : RAMEnv} (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (s : RAMState) :
    runBlock resInitX E s =
      xorState (s.pc + resInitX.length) (resDst E) (resSrc E) (resLen E) s.mem s.regs 0 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have h6 : (6 : ℕ) % 2 ^ E.W = 6 := Nat.mod_eq_of_lt (slot_lt hbig (by decide))
  have h7 : (7 : ℕ) % 2 ^ E.W = 7 := Nat.mod_eq_of_lt (slot_lt hbig (by decide))
  have h10 : (10 : ℕ) % 2 ^ E.W = 10 := Nat.mod_eq_of_lt (slot_lt hbig (by decide))
  apply ramState_eq_of
  · simp [resInitX, runBlock_cons, runBlock_nil, execInstr, xorState, resInitX_length]
  · simp [resInitX, runBlock_cons, runBlock_nil, execInstr, xorState, writeArray]
  · intro r
    fin_cases r <;>
      simp [resInitX, runBlock_cons, runBlock_nil, execInstr, xorState, resDst, resSrc, resLen,
        hdrCrBase, hdrResBase, hdrWords, h1, h6, h7, h10, Nat.zero_mod]

/-- **The repaired residual stage.** -/
def SresP (Ssketch : Stmt) (W M : ℕ) : Stmt :=
  .seq Ssketch (.seq (.code resInitX) (.seq xorStmt (.code (epilogue W M))))

theorem SresP_len (Ssketch : Stmt) (W M : ℕ) : (SresP Ssketch W M).len = Ssketch.len + 31 := by
  simp only [SresP, Stmt.len, resInitX_length, xorStmt_len, epilogue_length]

/-- `wordsOf W M ≤ M` for `M ≥ 1`: the word count never exceeds the bit count. -/
theorem wordsOf_le_self {W M : ℕ} (hW : 0 < W) (hM : 1 ≤ M) : wordsOf W M ≤ M := by
  unfold wordsOf
  have h : (M + W - 1) / W < M + 1 := by
    rw [Nat.div_lt_iff_lt_mul hW, Nat.succ_mul]
    have hMW : M ≤ M * W := Nat.le_mul_of_pos_right M hW
    omega
  omega

/-- The word count of an `M`-bit payload fits in a word as soon as `M` does. -/
theorem wordsOf_lt_two_pow {W M : ℕ} (hW : 0 < W) (hM : M < 2 ^ W) : wordsOf W M < 2 ^ W := by
  rcases Nat.eq_zero_or_pos M with h0 | hpos
  · subst h0
    unfold wordsOf
    have h : (0 + W - 1) / W = 0 := Nat.div_eq_of_lt (by omega)
    rw [h]
    exact Nat.two_pow_pos W
  · exact lt_of_le_of_lt (wordsOf_le_self hW hpos) hM

/-- Two exact runs compose, in the orientation this Mathlib's `Function.iterate_add_apply` has. -/
theorem iterate_two {α : Type} {f : α → α} {a b : ℕ} {x y z : α}
    (h1 : f^[a] x = y) (h2 : f^[b] y = z) : f^[a + b] x = z := by
  have e : f^[a + b] x = f^[b] (f^[a] x) := by
    rw [Nat.add_comm a b, Function.iterate_add_apply]
  rw [e, h1, h2]

/-- **The repaired `Sres` runs.**  From the residual array holding the packed stored syndrome and the
estimate buffer holding `x̂`, the stage runs `Ssketch`, the XOR and the epilogue, and delivers the
residual payload `a + CR x̂` at word `0` *in the repaired predicate* `DecInputOn`, with the `x̂` frame
intact.  Cost: `Tsk + 15 · wordsOf W M + 18`. -/
theorem stageRun_resCore {P : Program} {E : RAMEnv} {Ssketch : Stmt} {M m : ℕ} {xhatBase : ℕ}
    {Aset Bset : Finset ℕ} {estVec : Fin (E.W * m) → ZMod 2} {Tsk : ℝ} {a : ℕ}
    (hAt : At P a (Stmt.compile (SresP Ssketch E.W M) a))
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hMdet : M < 2 ^ E.W)
    (hDst : resDst E = 0) (hLen : resLen E = wordsOf E.W M)
    (hSrcLen : resSrc E + resLen E ≤ 2 ^ E.W)
    (hDisj : resSrc E + resLen E ≤ resDst E ∨ resDst E + resLen E ≤ resSrc E)
    (hFrame : resLen E ≤ xhatBase)
    (hSk : StageRun P E a (a + Ssketch.len) Tsk
      (fun s => HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec ∧
        writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem)
      (fun s => HoldsVec E.W M (resDst E) s (setVec M Bset) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec)) :
    StageRun P E a (a + (SresP Ssketch E.W M).len) (Tsk + (15 * (wordsOf E.W M : ℝ) + 18))
      (fun s => HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec ∧
        writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem)
      (fun s => DecInputOn E.W M 0 (setVec M (symmDiff Aset Bset)) [] s ∧
        HoldsVecPad E.W m xhatBase s estVec) := by
  intro s hpc hpre
  obtain ⟨hSkAt, hRest1⟩ := At.seqStmt hAt
  obtain ⟨hInitAt, hRest2⟩ := At.seqStmt hRest1
  obtain ⟨hXorAt, hEpiAt⟩ := At.seqStmt hRest2
  obtain ⟨k1, s1, hk1, hstep1, hpc1, hB1, hA1, hV1⟩ := hSk s hpc hpre
  have hMword : wordsOf E.W M < 2 ^ E.W := wordsOf_lt_two_pow (by omega) hMdet
  -- the layout facts the XOR needs
  have hLt : resLen E < 2 ^ E.W := by rw [hLen]; exact hMword
  have hDstL : resDst E + resLen E ≤ 2 ^ E.W := by rw [hDst]; simpa using hLt.le
  have hword : ∀ i < resLen E, s1.mem (resSrc E + i) < 2 ^ E.W := by
    intro i hi
    rw [hLen] at hi
    rw [hA1 i hi]
    exact RP.packMem_lt E.W (by omega) _ _
  have hwordd : ∀ i < resLen E, s1.mem (resDst E + i) < 2 ^ E.W := by
    intro i hi
    rw [hLen] at hi
    rw [hB1 i hi]
    exact RP.packMem_lt E.W (by omega) _ _
  -- the prologue
  have hinit : Sem P E (a + Ssketch.len) ((a + Ssketch.len) + 13) s1
      (fun k s' => k = 13 ∧
        s' = xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs 0) := by
    refine Sem.mono (Sem.block P E (a + Ssketch.len) resInitX s1 hInitAt resInitX_noBranch hpc1) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs, runBlock_resInitX hW hbig s1, resInitX_length, hpc1]
  -- the XOR
  have hxor : Sem P E ((a + Ssketch.len) + 13) (((a + Ssketch.len) + 13) + 15)
      (xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs 0)
      (fun k s' => k ≤ 15 * resLen E + 2 ∧
        s' = { xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs
                (resLen E) with pc := ((a + Ssketch.len) + 13) + 15 }) :=
    xorArray_spec P E ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs
      hXorAt hW hLt hDstL hSrcLen hDisj hword hwordd
  -- the epilogue
  have hepi : Sem P E (((a + Ssketch.len) + 13) + 15) ((((a + Ssketch.len) + 13) + 15) + 3)
      { xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs
          (resLen E) with pc := ((a + Ssketch.len) + 13) + 15 }
      (fun k s' => k = 3 ∧
        s' = runBlock (epilogue E.W M) E
          { xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs
              (resLen E) with pc := ((a + Ssketch.len) + 13) + 15 }) :=
    Sem.block P E (((a + Ssketch.len) + 13) + 15) (epilogue E.W M) _ hEpiAt
      (epilogue_noBranch E.W M) rfl
  obtain ⟨-, k2, s2, hstep2, hpc2, hk2, hQ2⟩ := hxor
  obtain ⟨-, k3, s3, hstep3, hpc3, hk3, hQ3⟩ := hepi
  obtain ⟨-, kI, sI, hstepI, hpcI, hkI, hQI⟩ := hinit
  -- the target states, spelled out
  set T1 : RAMState :=
    xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs 0 with hT1
  set T2 : RAMState :=
    { xorState ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E) s1.mem s1.regs (resLen E)
      with pc := ((a + Ssketch.len) + 13) + 15 } with hT2
  set T3 : RAMState := runBlock (epilogue E.W M) E T2 with hT3
  -- the three exact legs
  have hL1 : (step P E)^[13] s1 = T1 := by rw [← hkI, hstepI, hQI]
  have hL2 : (step P E)^[k2] T1 = T2 := by rw [hstep2, hQ2]
  have hL3 : (step P E)^[3] T2 = T3 := by rw [← hk3, hstep3, hQ3]
  have hs3 : s3 = T3 := hQ3
  -- the epilogue's effect
  obtain ⟨hE0, hE1, hE2, hEmem, hEpc⟩ := runBlock_epilogue (M := M) hW hMword T2
  have hT3_0 : T3.regs 0 = 0 := by rw [hT3]; exact hE0
  have hT3_1 : T3.regs 1 = wordsOf E.W M := by rw [hT3]; exact hE1
  have hT3_2 : T3.regs 2 = 0 := by rw [hT3]; exact hE2
  have hT3_mem : ∀ q, T3.mem q = T2.mem q := by intro q; rw [hT3]; exact congrFun hEmem q
  have hT3_pc : T3.pc = T2.pc + 3 := by rw [hT3]; exact hEpc
  have hT2_pc : T2.pc = ((a + Ssketch.len) + 13) + 15 := by rw [hT2]
  refine ⟨k1 + (13 + (k2 + 3)), s3, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hk2' : (k2 : ℝ) ≤ 15 * (resLen E : ℝ) + 2 := by exact_mod_cast hk2
    have hk1' : (k1 : ℝ) ≤ Tsk := hk1
    have hlen : (resLen E : ℝ) = (wordsOf E.W M : ℝ) := by rw [hLen]
    rw [hlen] at hk2'
    push_cast
    linarith
  · -- the run
    have h23 : (step P E)^[k2 + 3] T1 = T3 := iterate_two hL2 hL3
    rw [hs3]
    exact iterate_two hstep1 (iterate_two hL1 h23)
  · -- the exit address
    rw [hQ3, hT3_pc, hT2_pc, SresP_len]
    omega
  · -- the postcondition
    rw [hs3]
    refine ⟨⟨fun j hj => ?_, hT3_0, hT3_1, hT3_2⟩, fun j hj => ?_⟩
    · -- the payload is the packed symmetric difference
      have hjL : j < resLen E := by rw [hLen]; simpa using hj
      have hT2j : T2.mem j = s1.mem j ^^^ s1.mem (resSrc E + j) := by
        rw [hT2, hDst]
        have h := xorState_mem_get ((a + Ssketch.len) + 13) (resDst E) (resSrc E) (resLen E)
          s1.mem s1.regs j hjL
        rw [hDst, Nat.zero_add] at h
        exact h
      have hBj : s1.mem j = packMem E.W (setVec M Bset) j := by
        have hb := hB1 j (by omega)
        rwa [hDst, Nat.zero_add] at hb
      have hAj : s1.mem (resSrc E + j) = packMem E.W (setVec M Aset) j :=
        hA1 j (by simpa using hj)
      have hT3j : T3.mem j = packMem E.W (setVec M Bset) j ^^^ packMem E.W (setVec M Aset) j := by
        rw [hT3_mem j, hT2j, hBj, hAj]
      have hx : packMem E.W (setVec M Bset) j ^^^ packMem E.W (setVec M Aset) j
          = packMem E.W (setVec M (symmDiff Aset Bset)) j := by
        rw [packMem_setVec_symmDiff (by omega), Nat.xor_comm]
      rw [Nat.zero_add, hT3j, hx]
      simp only [hintMem]
      rw [if_pos (by simpa using hj)]
    · -- the `x̂` frame survives
      rw [hT3_mem (xhatBase + j)]
      have hT2f : T2.mem (xhatBase + j) = s1.mem (xhatBase + j) := by
        rw [hT2]
        exact xorState_mem_frame _ (resDst E) (resSrc E) (resLen E) s1.mem s1.regs _
          (Or.inr (by omega))
      rw [hT2f]
      exact hV1 j hj

/-- **The repaired `Sres` field**: the same `StageRun` at the address `compile` assigns it inside
`progDecOfTop`. -/
theorem stageRun_resP {Sini Srow Sdec Sassem' Scr Ssketch : Stmt} {E : RAMEnv} {M m : ℕ}
    {xhatBase : ℕ} {Aset Bset : Finset ℕ} {estVec : Fin (E.W * m) → ZMod 2} {Tsk : ℝ}
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hMdet : M < 2 ^ E.W)
    (hDst : resDst E = 0) (hLen : resLen E = wordsOf E.W M)
    (hSrcLen : resSrc E + resLen E ≤ 2 ^ E.W)
    (hDisj : resSrc E + resLen E ≤ resDst E ∨ resDst E + resLen E ≤ resSrc E)
    (hFrame : resLen E ≤ xhatBase)
    (hSk : StageRun (progDecOfTop Sini Srow Sdec Sassem' (SresP Ssketch E.W M) Scr) E
      (dResBase Sini Srow Sdec Sassem')
      (dResBase Sini Srow Sdec Sassem' + Ssketch.len) Tsk
      (fun s => HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec ∧
        writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem)
      (fun s => HoldsVec E.W M (resDst E) s (setVec M Bset) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec)) :
    StageRun (progDecOfTop Sini Srow Sdec Sassem' (SresP Ssketch E.W M) Scr) E
      (dResBase Sini Srow Sdec Sassem') (dCrBase Sini Srow Sdec Sassem' (SresP Ssketch E.W M))
      (Tsk + (15 * (wordsOf E.W M : ℝ) + 18))
      (fun s => HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W m xhatBase s estVec ∧
        writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem)
      (fun s => DecInputOn E.W M 0 (setVec M (symmDiff Aset Bset)) [] s ∧
        HoldsVecPad E.W m xhatBase s estVec) := by
  have hseq : At (progDecOfTop Sini Srow Sdec Sassem' (SresP Ssketch E.W M) Scr)
      (dAsBase Sini Srow Sdec)
      (Stmt.compile (Stmt.seq Sassem' (Stmt.seq (SresP Ssketch E.W M) Scr))
        (dAsBase Sini Srow Sdec)) :=
    at_seq_right (a := topLoop Sdec) (b := Stmt.seq Sassem' (Stmt.seq (SresP Ssketch E.W M) Scr))
      (at_col_seq Sini Srow Sdec Sassem' (SresP Ssketch E.W M) Scr)
  obtain ⟨-, hRest⟩ := At.seqStmt hseq
  obtain ⟨hAt, -⟩ := At.seqStmt hRest
  exact stageRun_resCore (a := dResBase Sini Srow Sdec Sassem') hAt hW hbig hMdet hDst hLen hSrcLen
    hDisj hFrame hSk

/-! ## 7. The repaired `Sassem` contract

Side A's `stageRun_as` is `CopyPre E dst src L → CopyPost E dst src L` with `L = asmLen E = det 0 = d`
words.  The reconciliation round identified three gaps against Side B's `as` field:

1. no **content** equation — nothing says the source words *are* the row transcripts;
2. no **frame** — `CopyPost` constrains only `[dst, dst + L)`, so nothing is known about the source
   words afterwards (the estimate buffer and the residual array both have to be carried);
3. the **length** — Side A moves `d` words, Side B asked for `wordsOf W sch.N`, which is a different
   payload (`packed_lt_padded_length`), not a different length of the same one.

The repair below keeps Side A's program (`Sassem = asmInit ++ copyStmt`, 24 instructions, `12d + 14`
steps, unchanged) and strengthens only the *contract*:

pre:  `CopyPre E dst src m` (the layout) **and** `HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref)`
      (the content: the column-output words are the row transcripts) **and** the residual array's
      content `HoldsVec E.W M (resSrc E) s (setVec M Aset)`;
post: `HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref)` (the padded `m`-word payload, which is
      exactly `res`'s `x̂` frame) **and** `CopyPost` **and** the residual array's content preserved.

The length is `m = det 0` words throughout, i.e. the `W * m`-bit padded payload — `HoldsVecPad`, not
`HoldsVec W sch.N`. -/

/-- The layout precondition of a word copy (Side A, verbatim): the source words are words, both
ranges lie inside the word bound `2 ^ W`, and the two ranges are disjoint. -/
def CopyPre (E : RAMEnv) (dst src L : ℕ) : RAMState → Prop := fun s =>
  (∀ i < L, s.mem (src + i) < 2 ^ E.W) ∧ src + L ≤ 2 ^ E.W ∧ dst + L ≤ 2 ^ E.W ∧
    (src + L ≤ dst ∨ dst + L ≤ src)

/-- The postcondition of a word copy (Side A, verbatim): the destination words are the source
words.  Nothing is said about the source range or the rest of memory — that is gap 2 of the
reconciliation; `stageRun_asCore` below proves the frame as well. -/
def CopyPost (E : RAMEnv) (dst src L : ℕ) : RAMState → Prop := fun s =>
  ∀ i < L, s.mem (dst + i) = s.mem (src + i)

/-- `det` slot 0: the row count `d`. -/
def hdrD : ℕ := 0
/-- `det` slot 5: the base of the assembled candidate array. -/
def hdrAsmBase : ℕ := 5
/-- `det` slot 9: the base of the column decoders' output words. -/
def hdrColOut : ℕ := 9

/-- The assembly base, as `det` gives it. -/
def asmDst (E : RAMEnv) : ℕ := E.det hdrAsmBase % 2 ^ E.W
/-- The assembly input base, as `det` gives it. -/
def asmSrc (E : RAMEnv) : ℕ := E.det hdrColOut % 2 ^ E.W
/-- The assembly length `d`, as `det` gives it. -/
def asmLen (E : RAMEnv) : ℕ := E.det hdrD % 2 ^ E.W

/-- `Sassem`'s prologue (Side A, verbatim): `r2 := dst` (slot 5), `r3 := src` (slot 9), `r1 := d`
(slot 0), the copy loop's scratch cleared. -/
def asmInit : List Instr :=
  [ iImm r15 hdrAsmBase, iTbl r2 r15,
    iImm r15 hdrColOut, iTbl r3 r15,
    iImm r15 hdrD, iTbl r1 r15,
    iImm r4 1, iImm r0 0, iImm r10 0, iImm r12 0, iImm r13 0, iImm r15 0 ]

lemma asmInit_noBranch : NoBranch asmInit := by
  simp [asmInit, NoBranch, Instr.NoBranchI]

lemma asmInit_length : asmInit.length = 12 := rfl

/-- Prefix assembly (Side A, verbatim): the `d`-word transfer of the row transcripts. -/
def SassemP : Stmt := .seq (.code asmInit) copyStmt

lemma SassemP_len : SassemP.len = 24 := by
  simp only [SassemP, Stmt.len, asmInit_length]
  rfl

/-- After the prologue the machine is in the copy loop's head state. -/
theorem runBlock_asmInit {E : RAMEnv} (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (s : RAMState) :
    runBlock asmInit E s =
      copyState (s.pc + asmInit.length) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs 0 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have h5 : (5 : ℕ) % 2 ^ E.W = 5 := Nat.mod_eq_of_lt (slot_lt hbig (by decide))
  have h9 : (9 : ℕ) % 2 ^ E.W = 9 := Nat.mod_eq_of_lt (slot_lt hbig (by decide))
  apply ramState_eq_of
  · simp [asmInit, runBlock_cons, runBlock_nil, execInstr, copyState, asmInit_length]
  · simp [asmInit, runBlock_cons, runBlock_nil, execInstr, copyState, writeArray]
  · intro r
    fin_cases r <;>
      simp [asmInit, runBlock_cons, runBlock_nil, execInstr, copyState, asmDst, asmSrc, asmLen,
        hdrAsmBase, hdrColOut, hdrD, h1, h5, h9, Nat.zero_mod]

/-- **`Sassem` runs, and its contract now carries the padded payload.**  The copy's exact final
state (`copyArray_spec`) gives both the destination words and the source frame, so the padded `m`-word
payload moves from `asmSrc` to `asmDst` while the residual array is untouched. -/
theorem stageRun_asCore {P : Program} {E : RAMEnv} {m M : ℕ} {pref : Fin m → List (ZMod 2)}
    {Aset : Finset ℕ} {a : ℕ}
    (hAt : At P a (Stmt.compile SassemP a))
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hWpos : 0 < E.W)
    (hLen : asmLen E = m) (hMdet : M < 2 ^ E.W)
    (hSep : asmDst E + m ≤ resSrc E) :
    StageRun P E a (a + SassemP.len) (12 * (m : ℝ) + 14)
      (fun s => CopyPre E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset))
      (fun s => HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
        CopyPost E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset)) := by
  intro s hpc hpre
  obtain ⟨hpreC, hsrcV, hAV⟩ := hpre
  have hMword : wordsOf E.W M < 2 ^ E.W := wordsOf_lt_two_pow (by omega) hMdet
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  -- the prologue
  have hsem1 : Sem P E a (a + 12) s
      (fun k s' => k = 12 ∧
        s' = copyState (a + 12) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs 0) := by
    refine Sem.mono (Sem.block P E a asmInit s hInitAt asmInit_noBranch hpc) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs, runBlock_asmInit hW hbig s, asmInit_length, hpc]
  -- the copy loop
  have hLt : asmLen E < 2 ^ E.W := Nat.mod_lt _ (by positivity)
  obtain ⟨hword, hsrcL, hdstL, hdisj⟩ := hpreC
  have hsem2 : Sem P E (a + 12) (a + 12 + 12)
      (copyState (a + 12) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs 0)
      (fun k s' => k ≤ 12 * asmLen E + 2 ∧
        s' = { copyState (a + 12) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs (asmLen E) with
                pc := a + 12 + 12 }) :=
    copyArray_spec P E (a + 12) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs hLoopAt hW hLt
      hdstL hsrcL hdisj hword
  obtain ⟨-, k1, s1, hstep1, hs1, hk1, hQ1⟩ := hsem1
  obtain ⟨-, k2, s2, hstep2, hs2, hk2, hQ2⟩ := hsem2
  refine ⟨k1 + k2, s2, ?_, ?_, ?_, ?_⟩
  · have hk1' : k1 = 12 := hk1
    have hk2' : (k2 : ℝ) ≤ 12 * (asmLen E : ℝ) + 2 := by exact_mod_cast hk2
    subst hk1'
    push_cast
    rw [show (12 : ℝ) * (m : ℝ) = 12 * (asmLen E : ℝ) from by rw [hLen]]
    linarith
  · rw [Nat.add_comm k1 k2, Function.iterate_add_apply, hstep1, hQ1, hstep2, hQ2]
  · rw [hQ2, SassemP_len]
  · -- the postcondition
    have hPost : s2 = { copyState (a + 12) (asmDst E) (asmSrc E) (asmLen E) s.mem s.regs
        (asmLen E) with pc := a + 12 + 12 } := hQ2
    have hmem : s2.mem = writeArray (asmDst E) s.mem (fun i => s.mem (asmSrc E + i)) (asmLen E) := by
      rw [hPost]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · -- the padded payload is at the destination
      rw [holdsVecPad_iff_words hWpos]
      intro j hj
      have hL' : j < asmLen E := by rw [hLen]; exact hj
      rw [hmem, writeArray_get (asmDst E) s.mem (fun i => s.mem (asmSrc E + i)) (asmLen E) j hL']
      exact hsrcV j (by rw [asm_words_eq_padded E.W m hWpos]; exact hj)
    · -- the copy postcondition
      intro i hi
      rw [hmem]
      rw [writeArray_get (asmDst E) s.mem (fun i => s.mem (asmSrc E + i)) (asmLen E) i hi,
        writeArray_frame (asmDst E) s.mem (fun i => s.mem (asmSrc E + i)) (asmLen E) (asmSrc E + i)]
      omega
    · -- the residual array is untouched
      intro j hj
      rw [hmem]
      rw [writeArray_frame (asmDst E) s.mem
        (fun i => s.mem (asmSrc E + i)) (asmLen E) (resSrc E + j) (by omega)]
      exact hAV j hj

/-- **The repaired `as` field**: `Sassem` at the address `compile` gives it, with the padded payload,
the content equation and the frame. -/
theorem stageRun_asP {Sini Srow Sdec Sres Scr : Stmt} {E : RAMEnv} {m M : ℕ}
    {pref : Fin m → List (ZMod 2)} {Aset : Finset ℕ}
    (hW : 1 < 2 ^ E.W) (hbig : 11 ≤ E.W) (hWpos : 0 < E.W)
    (hLen : asmLen E = m) (hMdet : M < 2 ^ E.W) (hSep : asmDst E + m ≤ resSrc E) :
    StageRun (progDecOfTop Sini Srow Sdec SassemP Sres Scr) E
      (dAsBase Sini Srow Sdec) (dResBase Sini Srow Sdec SassemP) (12 * (m : ℝ) + 14)
      (fun s => CopyPre E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset))
      (fun s => HoldsVecPad E.W m (asmDst E) s (asmVec E.W m pref) ∧
        CopyPost E (asmDst E) (asmSrc E) (asmLen E) s ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset)) := by
  have hseq : At (progDecOfTop Sini Srow Sdec SassemP Sres Scr) (dAsBase Sini Srow Sdec)
      (Stmt.compile (Stmt.seq SassemP (Stmt.seq Sres Scr)) (dAsBase Sini Srow Sdec)) :=
    at_seq_right (a := topLoop Sdec) (b := Stmt.seq SassemP (Stmt.seq Sres Scr))
      (at_col_seq Sini Srow Sdec SassemP Sres Scr)
  obtain ⟨hAt, -⟩ := At.seqStmt hseq
  exact stageRun_asCore (a := dAsBase Sini Srow Sdec) hAt hW hbig hWpos hLen hMdet hSep
/-! ## 8. The added calling-convention conjunct is inhabited

The new conjunct is a genuine caller obligation, not a contradiction.  It is
* implied by any zeroed destination block (`hSkPre_of`), and
* satisfied at every degenerate `wordsOf W M = 0` instance (`zeroed_of_wordsOf_zero`), which is the
  instance the §9 model of `_65_repair_block` uses, and
* satisfiable at *every* `M`, by zeroing the block (`zeroed_inhabited`).
-/

/-- Any state whose destination block is zeroed satisfies the new conjunct (definitional form). -/
theorem hSkPre_of {E : RAMEnv} {M m : ℕ} {Aset : Finset ℕ} {xhatBase : ℕ}
    {estVec : Fin (E.W * m) → ZMod 2} {s : RAMState}
    (h1 : HoldsVec E.W M (resSrc E) s (setVec M Aset))
    (h2 : HoldsVecPad E.W m xhatBase s estVec)
    (hz : writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem) :
    HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
      HoldsVecPad E.W m xhatBase s estVec ∧
      writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem :=
  ⟨h1, h2, hz⟩

/-- The conjunct holds at every `wordsOf W M = 0` instance: zeroing `0` words is the identity. -/
theorem zeroed_of_wordsOf_zero {E : RAMEnv} {M : ℕ} (rd : ℕ) (m : ℕ → ℕ)
    (h : wordsOf E.W M = 0) : writeArray rd m (fun _ => 0) (wordsOf E.W M) = m := by
  rw [h]
  simp [writeArray]

/-- **The conjunct is satisfiable at every `M`**: zeroing the destination block and then re-zeroing
it is the same state.  So the strengthened contract is not vacuous. -/
theorem zeroed_inhabited (E : RAMEnv) (M : ℕ) (rd : ℕ) (m : ℕ → ℕ) :
    writeArray rd (writeArray rd m (fun _ => 0) (wordsOf E.W M)) (fun _ => 0) (wordsOf E.W M)
      = writeArray rd m (fun _ => 0) (wordsOf E.W M) := by
  funext a
  by_cases h : a < rd ∨ rd + wordsOf E.W M ≤ a
  · rw [writeArray_frame _ _ _ _ _ h, writeArray_frame _ _ _ _ _ h]
  · push_neg at h
    obtain ⟨h1, h2⟩ := h
    have hae : a = rd + (a - rd) := by omega
    conv_lhs => rw [hae]
    conv_rhs => rw [hae]
    rw [writeArray_get rd (writeArray rd m (fun _ => 0) (wordsOf E.W M)) (fun _ => 0)
        (wordsOf E.W M) (a - rd) (by omega),
      writeArray_get rd m (fun _ => 0) (wordsOf E.W M) (a - rd) (by omega)]


/-! ## 9. The `hSk` conjunct, propagated through the six stage contracts

`_65_repair_hSk` put the sketch's calling convention

  `writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem`

into the *precondition* of `stageRun_resCore`/`stageRun_resP` (the `res` stage), and proved it
inhabited (`zeroed_inhabited`, `zeroed_of_wordsOf_zero`).  But the two contracts it must compose
with — the column stage's post (which is also the assembly stage's pre), `ColOutAs`, and the
six-field structure, `TopDecStagesP` — did **not** carry it, so `hS.res` could not be applied to
`hS.as`'s output: the contracts did not compose.

This section propagates it:

* `ColOutAsZ` is `ColOutAs` **plus** the conjunct: the column stage (= the top-level caller of
  `Sres`) is required to leave the CR payload block zeroed;
* the assembly stage's post carries it — mathematically because the assembly's only write is the
  word copy into `asmDst E`, and `dstZero_writeArray` proves that a write confined to a block
  disjoint from `[resDst, resDst + wordsOf E.W M)` preserves a zeroed block;
* the `res` field's precondition is then *literally* `stageRun_resP`'s precondition, so the conjunct
  reaches `hSk` verbatim;
* `topDecCorrects_of_stagesZ` is the composition with the conjunct threaded through, i.e. the same
  statement as `_65_repair_block`'s `topDecCorrects_of_stagesP` at a structure that now
  composes.

§10 records non-vacuity: the six fields (with the new conjunct) are inhabited at the same model as
`_65_repair_block` §9, and the strengthened sketch precondition is inhabited at a **non-degenerate**
instance (`M = 1`, `wordsOf 12 1 = 1`) where the zeroed block is a genuine word. -/

/-- **The sketch's calling convention**, as a state predicate: the CR payload block is zeroed. -/
def DstZero (E : RAMEnv) (M : ℕ) (s : RAMState) : Prop :=
  writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) = s.mem

/-- Inside the block, a zeroed payload really is zero. -/
theorem dstZero_word {E : RAMEnv} {M : ℕ} {s : RAMState} {a : ℕ} (h : DstZero E M s)
    (h1 : resDst E ≤ a) (h2 : a < resDst E + wordsOf E.W M) : s.mem a = 0 := by
  have hi : a - resDst E < wordsOf E.W M := by omega
  have hae : resDst E + (a - resDst E) = a := by omega
  calc s.mem a = writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) a := by rw [h]
    _ = writeArray (resDst E) s.mem (fun _ => 0) (wordsOf E.W M) (resDst E + (a - resDst E)) := by
          rw [hae]
    _ = 0 := writeArray_get _ _ _ _ _ hi

/-- The pointwise form of `DstZero`. -/
theorem dstZero_iff {E : RAMEnv} {M : ℕ} {s : RAMState} :
    DstZero E M s ↔ ∀ a, resDst E ≤ a → a < resDst E + wordsOf E.W M → s.mem a = 0 := by
  constructor
  · intro h a h1 h2
    exact dstZero_word h h1 h2
  · intro h
    funext a
    by_cases ha : a < resDst E ∨ resDst E + wordsOf E.W M ≤ a
    · rw [writeArray_frame _ _ _ _ _ ha]
    · have h1 : resDst E ≤ a := by omega
      have h2 : a < resDst E + wordsOf E.W M := by omega
      have hae : resDst E + (a - resDst E) = a := by omega
      conv_lhs => rw [← hae]
      rw [writeArray_get _ _ _ _ _ (by omega : a - resDst E < wordsOf E.W M), h _ h1 h2]

/-- The conjunct is free when the payload occupies no words. -/
theorem dstZero_of_wordsOf_zero {E : RAMEnv} {M : ℕ} (h : wordsOf E.W M = 0) (s : RAMState) :
    DstZero E M s :=
  zeroed_of_wordsOf_zero (resDst E) s.mem h

/-- **The assembly cannot disturb the zeroed CR payload.**  A write confined to a block disjoint from
`[resDst, resDst + wordsOf E.W M)` preserves `DstZero`.  This is the mathematical content of "the
assembly stage's post carries the conjunct": `SassemP`'s only memory effect is a `writeArray` into
`asmDst E`, so the disjointness hypothesis holds as soon as `asmDst E + m ≤ resDst E` (or the
reverse), which is exactly the layout constraint the caller must respect. -/
theorem dstZero_writeArray {E : RAMEnv} {M base L : ℕ} {f : ℕ → ℕ} {m : ℕ → ℕ}
    (hsep : base + L ≤ resDst E ∨ resDst E + wordsOf E.W M ≤ base)
    (h : writeArray (resDst E) m (fun _ => 0) (wordsOf E.W M) = m) :
    writeArray (resDst E) (writeArray base m f L) (fun _ => 0) (wordsOf E.W M)
      = writeArray base m f L := by
  funext a
  by_cases ha : a < resDst E ∨ resDst E + wordsOf E.W M ≤ a
  · rw [writeArray_frame _ _ _ _ _ ha]
  · have h1 : resDst E ≤ a := by omega
    have h2 : a < resDst E + wordsOf E.W M := by omega
    have hbase : a < base ∨ base + L ≤ a := by
      rcases hsep with hs | hs
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hae : resDst E + (a - resDst E) = a := by omega
    conv_lhs => rw [← hae]
    rw [writeArray_get _ _ _ _ _ (by omega : a - resDst E < wordsOf E.W M),
      writeArray_frame base m f L a hbase]
    exact (dstZero_word (s := ⟨0, fun _ => 0, m⟩) h h1 h2).symm

/-- Weakening a stage's postcondition. -/
theorem stageRun_post {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I Q Q' : RAMState → Prop}
    (h : StageRun P E a b T I Q) (hQ : ∀ s, Q s → Q' s) : StageRun P E a b T I Q' := by
  intro s hpc hI
  obtain ⟨k, s', hk, hstep, hb, hQ'⟩ := h s hpc hI
  exact ⟨k, s', hk, hstep, hb, hQ s' hQ'⟩

/-- Weakening a stage's precondition. -/
theorem stageRun_pre {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I I' Q : RAMState → Prop}
    (h : StageRun P E a b T I' Q) (hI : ∀ s, I s → I' s) : StageRun P E a b T I Q := by
  intro s hpc hI'
  exact h s hpc (hI s hI')

/-- **The column stage's post / assembly stage's pre, with the calling convention.**  Verbatim
`ColOutAs` plus `DstZero E M`: the caller (the column stage) must leave the CR payload block zeroed,
because `Sres`'s sketch accumulates into it instead of overwriting it. -/
def ColOutAsZ (E : RAMEnv) (m M : ℕ) (Aset : Finset ℕ) (s : RAMState)
    (pref : Fin m → List (ZMod 2)) : Prop :=
  CopyPre E (asmDst E) (asmSrc E) m s ∧
    HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
    HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
    DstZero E M s

/-- `ColOutAs` is recovered from `ColOutAsZ` by dropping the new conjunct. -/
theorem colOutAs_of_colOutAsZ {E : RAMEnv} {m M : ℕ} {Aset : Finset ℕ} {s : RAMState}
    {pref : Fin m → List (ZMod 2)} (h : ColOutAsZ E m M Aset s pref) :
    CopyPre E (asmDst E) (asmSrc E) m s ∧
      HoldsVecPad E.W m (asmSrc E) s (asmVec E.W m pref) ∧
      HoldsVec E.W M (resSrc E) s (setVec M Aset) :=
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The six stage contracts of §9.2's decoder, repaired and with the calling convention carried.**
The differences from `_65_repair_block`'s `TopDecStagesP` are exactly the propagation of the `hSk`
conjunct:

* the `col` field's post (and the `as` field's pre) is `ColOutAsZ`, which demands the zeroed CR
  payload;
* the `as` field's post carries `DstZero` forward (the assembly only writes `asmDst E`, so
  `dstZero_writeArray` discharges it at the program level);
* the `res` field's precondition is exactly `stageRun_resP`'s, so the conjunct is handed to `hSk`. -/
structure TopDecStagesZ (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (sch : RowScheme)
    (lr : sch.LocalSeed) {M : ℕ} (J : Finset ℕ)
    (D : (Fin sch.N → ZMod 2) → Fin M → ZMod 2)
    (RowOut : RAMState → Prop) (Aset Bset S : Finset ℕ) (CR : CRFamily) (t : ℕ)
    (x : Fin sch.N → ZMod 2) (Tini Trow Tdec Tas Tres Tcr : ℝ) : Prop where
  /-- **`Sinit`**, the prologue: from `decoderStart` to the row loop's head. -/
  init : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
    (fun s => s = decoderStart E.W (D x) []) (RowIn sch.m)
  /-- **`Srow`**, `d` calls of Proposition 2.1's decoder. -/
  row : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit)
    (dColBase Sinit Srow) Trow (RowIn sch.m) (fun s => RowOut s ∧ ColIn sch.ℓ s)
  /-- **`Sdec`**, the `ℓ` child decoders, leaving the row transcripts, the residual array **and the
  zeroed CR payload**. -/
  col : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
    (dAsBase Sinit Srow Sdec) Tdec (fun s => RowOut s ∧ ColIn sch.ℓ s)
    (fun s => ColOutAsZ E sch.m M Aset s
      (fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr (supp x) j) sch.ℓ))
  /-- **`Sassem`**: the padded `m`-word payload `asmVec E.W sch.m pref` moves to `asmDst E`, the
  residual array is untouched, **and the zeroed CR payload survives**. -/
  as : ∀ pref : Fin sch.m → List (ZMod 2),
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
      (dResBase Sinit Srow Sdec Sassem) Tas (fun s => ColOutAsZ E sch.m M Aset s pref)
      (fun s => HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref) ∧
        HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧ DstZero E M s)
  /-- **`Sres`**, residual-syndrome formation: `a + CR x̂` at word `0`, in the *repaired* predicate,
  with the `x̂` frame.  Its precondition is `stageRun_resP`'s to the letter. -/
  res : ∀ pref : Fin sch.m → List (ZMod 2),
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dResBase Sinit Srow Sdec Sassem) (dCrBase Sinit Srow Sdec Sassem Sres) Tres
      (fun s => HoldsVec E.W M (resSrc E) s (setVec M Aset) ∧
        HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref) ∧ DstZero E M s)
      (fun s => DecInputOn E.W M 0 (setVec M (symmDiff Aset Bset)) [] s ∧
        HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref))
  /-- **`Scr`**, Proposition 2.3's decoder at the residual `S`, plus the final merge `x̂ + ê`. -/
  cr : ∀ pref : Fin sch.m → List (ZMod 2),
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
      (fun s => DecInputOn E.W M 0 (setVec M (CR.sketch sch.N t S)) [] s ∧
        HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref))
      (fun s => OutListIs s (symmDiff (sch.assembled lr J pref) S))

/-- `x̂ + (x + x̂) = x`. -/
theorem symmDiff_self_cancel (a b : Finset ℕ) : symmDiff a (symmDiff b a) = b := by
  ext v
  simp only [mem_symmDiff]
  tauto

theorem symmDiff_empty_empty : symmDiff (∅ : Finset ℕ) ∅ = ∅ := by
  ext v
  simp [mem_symmDiff]

theorem symmDiff_empty_right (S : Finset ℕ) : symmDiff S ∅ = S := by
  ext v
  simp [mem_symmDiff]

theorem step_halt_self {P : Program} {E : RAMEnv} {s : RAMState} (h : P[s.pc]? = some .halt) :
    step P E s = s := by
  simp [step, h]

theorem step_iterate_halt {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some .halt) (k : ℕ) : (step P E)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (step P E)^[k + 1] s = s
      rw [Function.iterate_succ_apply, step_halt_self h, ih]

theorem halted_iff {P : Program} {s : RAMState} : Halted P s ↔ P[s.pc]? = some .halt := by
  unfold Halted
  cases h : P[s.pc]? with
  | none => simp
  | some i => cases i <;> simp

/-- The trailing `halt` of the composite decoder sits at `dEnd`. -/
theorem halt_at_dEnd {Sinit Srow Sdec Sassem Sres Scr : Stmt} :
    (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[dEnd Sinit Srow Sdec Sassem Sres Scr]? =
      some Instr.halt := by
  have hlen : dEnd Sinit Srow Sdec Sassem Sres Scr =
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0).length := by
    rw [Stmt.length_compile]
    simp only [dEnd, dCrBase, dResBase, dAsBase, dColBase, dRowBase, topDecStmt, topLoop, Stmt.len]
    omega
  rw [hlen]
  rw [show progDecOfTop Sinit Srow Sdec Sassem Sres Scr =
      (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt] from rfl,
    List.getElem?_append_right (le_refl _)]
  simp

/-- **The composition, with the calling convention propagated.**  The chain is
`init → row → col → as → res → cr`; the pass from `as` to `res` is where the conjunct matters: the
`as` post supplies `DstZero E M`, which is exactly the third conjunct of `res`'s precondition, which
in turn is `hSk`'s.  The residual payload `a + CR x̂` is rewritten to `CR (x + x̂)` by the syndrome's
additivity (`hAdd`), the CR stage decodes it, and the final merge `x̂ + (x + x̂) = x` is
`symmDiff_self_cancel`. -/
theorem topDecCorrects_of_stagesZ {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {M : ℕ} {sch : RowScheme} {lr : sch.LocalSeed} {J : Finset ℕ}
    {D : (Fin sch.N → ZMod 2) → Fin M → ZMod 2} {RowOut : RAMState → Prop}
    {CR : CRFamily} {t : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (hAdd : ∀ A B : Finset ℕ, CR.sketch sch.N t (symmDiff A B)
      = symmDiff (CR.sketch sch.N t A) (CR.sketch sch.N t B))
    (h : ∀ x : Fin sch.N → ZMod 2,
      TopDecStagesZ Sinit Srow Sdec Sassem Sres Scr E sch lr J D RowOut
        (CR.sketch sch.N t (supp x)) (CR.sketch sch.N t (sch.exactEstimate lr (supp x) J))
        (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)) CR t x
        Tini Trow Tdec Tas Tres Tcr) :
    TopDecCorrects Sinit Srow Sdec Sassem Sres Scr E D
      (Tini + Trow + Tdec + Tas + Tres + Tcr) := by
  intro x s' ⟨k, hk, hstep, hhalt⟩
  obtain hS := h x
  have hchain : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr)
      (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart E.W (D x) [])
      (fun s => OutListIs s (symmDiff (sch.exactEstimate lr (supp x) J)
        (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)))) := by
    set pref : Fin sch.m → List (ZMod 2) :=
      fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr (supp x) j) sch.ℓ with hpref
    have hxhat : sch.assembled lr J pref = sch.exactEstimate lr (supp x) J := rfl
    have hAs' : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dAsBase Sinit Srow Sdec) (dResBase Sinit Srow Sdec Sassem) Tas
        (fun s => ColOutAsZ E sch.m M (CR.sketch sch.N t (supp x)) s pref)
        (fun s => HoldsVec E.W M (resSrc E) s (setVec M (CR.sketch sch.N t (supp x))) ∧
          HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref) ∧ DstZero E M s) :=
      stageRun_post (hS.as pref) (fun s hs => ⟨hs.2.1, hs.1, hs.2.2⟩)
    have hA : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
        (dResBase Sinit Srow Sdec Sassem) (Tini + Trow + Tdec + Tas)
        (fun s => s = decoderStart E.W (D x) [])
        (fun s => HoldsVec E.W M (resSrc E) s (setVec M (CR.sketch sch.N t (supp x))) ∧
          HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref) ∧ DstZero E M s) :=
      ((hS.init.trans hS.row).trans hS.col).trans hAs'
    have hB : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dResBase Sinit Srow Sdec Sassem) (dCrBase Sinit Srow Sdec Sassem Sres) Tres
        (fun s => HoldsVec E.W M (resSrc E) s (setVec M (CR.sketch sch.N t (supp x))) ∧
          HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref) ∧ DstZero E M s)
        (fun s => DecInputOn E.W M 0
          (setVec M (CR.sketch sch.N t (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)))) [] s
          ∧ HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref)) := by
      refine stageRun_post (hS.res pref) ?_
      intro s hs
      obtain ⟨hdec, hframe⟩ := hs
      have hvec : symmDiff (CR.sketch sch.N t (supp x))
          (CR.sketch sch.N t (sch.exactEstimate lr (supp x) J))
          = CR.sketch sch.N t (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)) :=
        (hAdd (supp x) (sch.exactEstimate lr (supp x) J)).symm
      rw [hvec] at hdec
      exact ⟨hdec, hframe⟩
    have hC : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
        (fun s => DecInputOn E.W M 0
          (setVec M (CR.sketch sch.N t (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)))) [] s
          ∧ HoldsVecPad E.W sch.m (asmDst E) s (asmVec E.W sch.m pref))
        (fun s => OutListIs s (symmDiff (sch.exactEstimate lr (supp x) J)
          (symmDiff (supp x) (sch.exactEstimate lr (supp x) J)))) :=
      stageRun_post (hS.cr pref) (fun s hs => by rw [hxhat] at hs; exact hs)
    exact (hA.trans hB).trans hC
  have hfin : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr)
      (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart E.W (D x) [])
      (fun s => OutListIs s (supp x)) := by
    refine stageRun_post hchain ?_
    intro s hs
    rw [symmDiff_self_cancel] at hs
    exact hs
  obtain ⟨k', s₁, hk', hrun, hpc, hQ⟩ := hfin (decoderStart E.W (D x) []) rfl rfl
  have hhalt₁ : (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[s₁.pc]? = some Instr.halt := by
    rw [hpc]
    exact halt_at_dEnd
  have hs'h : (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[s'.pc]? = some Instr.halt :=
    halted_iff.mp hhalt
  have hEq : s' = s₁ := by
    rcases le_total k k' with hle | hle
    · have hk'k : k' - k + k = k' := Nat.sub_add_cancel hle
      have h1 : s₁ = (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k' - k] s' := by
        rw [← hrun, ← hstep, ← Function.iterate_add_apply, hk'k]
      rw [h1, step_iterate_halt hs'h]
    · have hkk : k - k' + k' = k := Nat.sub_add_cancel hle
      have h1 : s' = (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k - k'] s₁ := by
        rw [← hstep, ← hrun, ← Function.iterate_add_apply, hkk]
      rw [h1, step_iterate_halt hhalt₁]
  subst hEq
  exact outputsSupport_iff_outListIs s' x |>.mpr hQ

/-- **The correctness half of conjunct 8, per seed**, with the propagated structure. -/
def TopDecCorrectsSeedZ {ι : Type} (Sinit Srow Sdec Sassem Sres Scr : Stmt) (env : ι → RAMEnv)
    {n M : ℕ} (D : ι → (Fin n → ZMod 2) → Fin M → ZMod 2) (Tdec : ℝ) : Prop :=
  ∀ (i : ι) (x : Fin n → ZMod 2) (s' : RAMState),
    (∃ k : ℕ, (k : ℝ) ≤ Tdec ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (env i))^[k]
        (decoderStart (env i).W (D i x) []) = s' ∧
      Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
    OutputsSupport s' x

/-- **The composition, over the seeds of the family.** -/
theorem topDecCorrectsSeed_of_stagesZ {ι : Type} {Sinit Srow Sdec Sassem Sres Scr : Stmt}
    {env : ι → RAMEnv} {M : ℕ} {sch : RowScheme} (lr : ι → sch.LocalSeed) {J : Finset ℕ}
    (D : ι → (Fin sch.N → ZMod 2) → Fin M → ZMod 2)
    (RowOut : ι → RAMState → Prop) (CR : CRFamily) (t : ℕ)
    {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (hAdd : ∀ (i : ι) (A B : Finset ℕ), CR.sketch sch.N t (symmDiff A B)
      = symmDiff (CR.sketch sch.N t A) (CR.sketch sch.N t B))
    (h : ∀ (i : ι) (x : Fin sch.N → ZMod 2),
      TopDecStagesZ Sinit Srow Sdec Sassem Sres Scr (env i) sch (lr i) J (D i) (RowOut i)
        (CR.sketch sch.N t (supp x)) (CR.sketch sch.N t (sch.exactEstimate (lr i) (supp x) J))
        (symmDiff (supp x) (sch.exactEstimate (lr i) (supp x) J)) CR t x
        Tini Trow Tdec Tas Tres Tcr) :
    TopDecCorrectsSeedZ Sinit Srow Sdec Sassem Sres Scr env D
      (Tini + Trow + Tdec + Tas + Tres + Tcr) :=
  fun i => topDecCorrects_of_stagesZ (hAdd i) (h i)

/-! ## 10. Non-vacuity of the propagated contract

Two independent checks, because the project has been burnt by contradictory hypotheses:

* §10.1 exhibits a model of **all six fields of `TopDecStagesZ`**, i.e. the strengthened structure is
  consistent.  As in `_65_repair_block` §9 the tree side is degenerate (`N = 0`), but the
  deterministic side uses the *real* repaired programs `SassemP` and `SresP`, and the `as`/`res`
  fields are the real `stageRun_asP`/`stageRun_resP` theorems.  With `M = 0` the new conjunct is
  free (`wordsOf 12 0 = 0`), which is exactly `dstZero_of_wordsOf_zero`.
* §10.2 shows the conjunct is **not** vacuous: at `M = 1`, `W = 12` the zeroed block is one genuine
  word (`wordsOf 12 1 = 1`), and the full `hSk` precondition — `HoldsVec` at `resSrc`, the `HoldsVecPad`
  frame, and the zeroed block — has an explicit inhabitant.  So the strengthened `res`/`hSk`
  precondition is satisfiable where `wordsOf W M > 0`, not only in the degenerate model.
* §10.3 records the program-level preservation fact used by the `as` field: if a stage's memory
  effect is a copy into `asmDst E` and `asmDst E` is disjoint from the payload block, then a zeroed
  payload stays zeroed.  (`dstZero_writeArray` is the general form; the corollary below is the
  `SassemP` shape.) -/

/-! ### 10.1 A model of all six fields of `TopDecStagesZ` -/

/-- The universe-`0` row scheme: `N = m = ℓ = 0`, one trivial random coin. -/
def sch0 : RowScheme where
  N := 0
  m := 0
  ℓ := 0
  Rand := Unit
  ft := inferInstance
  ne := inferInstance
  code := fun j => j.elim0
  code_linear := fun j => j.elim0
  predict := fun j => j.elim0
  final := fun j => j.elim0

@[simp] theorem sch0_N : sch0.N = 0 := rfl
@[simp] theorem sch0_m : sch0.m = 0 := rfl
@[simp] theorem sch0_ell : sch0.ℓ = 0 := rfl

/-- The (unique) local seed of `sch0`. -/
def lr0 : sch0.LocalSeed := ⟨Equiv.refl (Fin 0), fun j => j.elim0⟩

/-- The empty CR family: no rows, so every syndrome is empty. -/
def cr0 : CRFamily where
  rows := fun _ _ => 0
  col := fun _ _ _ => ∅
  dec := fun _ _ _ => none

/-- The all-zero decoder environment with `W = 12`: every header slot is `0`. -/
def E0 : RAMEnv := detEnv 12 (fun _ => 0)

@[simp] theorem E0_W : E0.W = 12 := rfl

@[simp] theorem E0_det (k : ℕ) : E0.det k = 0 := rfl

@[simp] theorem E0_asmDst : asmDst E0 = 0 := by simp [asmDst, E0, detEnv]

@[simp] theorem E0_asmSrc : asmSrc E0 = 0 := by simp [asmSrc, E0, detEnv]

@[simp] theorem E0_asmLen : asmLen E0 = 0 := by simp [asmLen, E0, detEnv]

@[simp] theorem E0_resDst : resDst E0 = 0 := by simp [resDst, E0, detEnv]

@[simp] theorem E0_resSrc : resSrc E0 = 0 := by simp [resSrc, E0, detEnv]

@[simp] theorem E0_resLen : resLen E0 = 0 := by simp [resLen, E0, detEnv]

theorem wordsOf_zero (W : ℕ) : wordsOf W 0 = 0 := by
  unfold wordsOf
  rcases Nat.eq_zero_or_pos W with h | h
  · subst h
    simp
  · exact Nat.div_eq_of_lt (by omega)

/-- The padded length of the empty payload. -/
@[simp] theorem E0_wordsOf_pad : wordsOf E0.W (E0.W * 0) = 0 := by
  rw [E0_W, Nat.mul_zero, wordsOf_zero]

theorem sch0_assembled (J : Finset ℕ) (pref : Fin sch0.m → List (ZMod 2)) :
    sch0.assembled lr0 J pref = ∅ := by
  haveI : IsEmpty (Fin sch0.N) := by
    rw [sch0_N]
    infer_instance
  simp [RowScheme.assembled, assemble]
  rfl

theorem sch0_exactEstimate (J : Finset ℕ) (X : Finset ℕ) :
    sch0.exactEstimate lr0 X J = ∅ := by
  simp only [RowScheme.exactEstimate]
  exact sch0_assembled J _

theorem sch0_supp (x : Fin sch0.N → ZMod 2) : supp x = ∅ := by
  haveI : IsEmpty (Fin sch0.N) := by
    rw [sch0_N]
    infer_instance
  simp [supp]
  rfl

theorem cr0_sketch (N t : ℕ) (X : Finset ℕ) : cr0.sketch N t X = ∅ := by
  simp [CRFamily.sketch, cr0]

/-- `col`'s postcondition holds at every state when `m = M = 0`: every word bound is vacuous, the
copy has length `0`, and the payload block is empty. -/
theorem colOutAsZ_zero (Aset : Finset ℕ) (s : RAMState) (pref : Fin 0 → List (ZMod 2)) :
    ColOutAsZ E0 0 0 Aset s pref := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i hi; omega
  · simp
  · simp
  · exact Or.inr (by simp)
  · intro j hj
    rw [E0_wordsOf_pad] at hj
    omega
  · intro j hj
    rw [wordsOf_zero] at hj
    omega
  · exact dstZero_of_wordsOf_zero (by rw [wordsOf_zero]) s

/-- The zero-length loop test fails immediately: the counter `r1 = 0` is not below the bound. -/
theorem d65Cond_zero_false {s : RAMState} (h1 : s.regs 1 = 0) (h2 : s.regs 2 = 0) :
    ¬ d65Cond.eval s := by
  simp [d65Cond, Cond.eval, h1, h2]

/-- **A model of all six fields of `TopDecStagesZ`.**  `Aset`, `Bset` are arbitrary (with `M = 0`
every `HoldsVec` is vacuous); `S` is empty.  The two deterministic programs are the *real* repaired
ones, `SassemP` and `SresP`, and the `as`/`res` fields are `stageRun_asP`/`stageRun_resP`. -/
theorem stagesZ_model (x : Fin sch0.N → ZMod 2) (Aset Bset S : Finset ℕ) (hS : S = ∅) :
    TopDecStagesZ (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0) (.code [])
      E0 sch0 lr0 (J := ∅) (M := 0) (D := fun _ => fun i : Fin 0 => i.elim0)
      (RowOut := fun _ => True) Aset Bset S cr0 0 x 0 2 2 14 18 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `init`: the empty prologue, `0` steps
    intro s hpc hpre
    refine ⟨0, s, by norm_num, rfl, ?_, ?_⟩
    · rw [hpc]
      simp [dRowBase, Stmt.len]
    · rw [hpre]
      refine ⟨?_, ?_⟩ <;> simp [decoderStart, initState, wordsOf_zero]
  · -- `row`: the `d = 0` loop exits after its test
    intro s hpc hpre
    obtain ⟨h1, h2⟩ := hpre
    have h2' : s.regs 2 = 0 := by rw [h2, sch0_m]
    have hstop : ¬ d65Cond.eval s := d65Cond_zero_false h1 h2'
    have hAt := at_row_loop (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0)
      (.code [])
    obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ :=
      Sem.loopExit (progDecOfTop (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0)
        (.code [])) E0 (dRowBase (.code [])) d65Cond
        (.seq (.code []) (.code d65Inc)) s hAt (by norm_num) hpc hstop
    refine ⟨k, s', ?_, hstep, ?_, trivial, ?_⟩
    · rw [hk]; norm_num [d65Cond, Cond.code]
    · rw [hpc']
      simp [dColBase, dRowBase, topLoop, d65Cond, Cond.code, Stmt.len]
    · rw [hs']
      refine ⟨?_, ?_⟩ <;>
        simp [d65Cond, Cond.code, runBlock_cons, runBlock_nil, execInstr, h1, h2', Nat.zero_mod]
  · -- `col`: the same, and `col`'s postcondition is vacuous at `m = M = 0`
    intro s hpc hpre
    obtain ⟨-, h1, h2⟩ := hpre
    have h2' : s.regs 2 = 0 := by rw [h2, sch0_ell]
    have hstop : ¬ d65Cond.eval s := d65Cond_zero_false h1 h2'
    have hAt := at_col_loop (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0)
      (.code [])
    obtain ⟨-, k, s', hstep, hpc', hk, hs'⟩ :=
      Sem.loopExit (progDecOfTop (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0)
        (.code [])) E0 (dColBase (.code []) (.code [])) d65Cond
        (.seq (.code []) (.code d65Inc)) s hAt (by norm_num) hpc hstop
    refine ⟨k, s', ?_, hstep, ?_, ?_⟩
    · rw [hk]; norm_num [d65Cond, Cond.code]
    · rw [hpc']
      simp [dAsBase, dColBase, dRowBase, topLoop, d65Cond, Cond.code, Stmt.len] <;> omega
    · exact colOutAsZ_zero _ s' _
  · -- `as`: the real `Sassem`, with the zeroed-payload conjunct carried forward
    intro pref
    -- `stageRun_asP` at `m = 0`: its `CopyPre`/`CopyPost` still mention `asmLen E`, so supply the
    -- copy precondition at the *actual* length (which is `0`) and rebuild the post at length `0`.
    have h := stageRun_asP (Sini := (.code [])) (Srow := (.code [])) (Sdec := (.code []))
      (Sres := SresP (.code []) 12 0) (Scr := (.code [])) (E := E0) (m := 0) (M := 0)
      (pref := pref) (Aset := Aset) (by norm_num) (by norm_num) (by norm_num)
      (by simp) (by norm_num) (by simp)
    intro s hpc hs
    have hCopyPre : CopyPre E0 (asmDst E0) (asmSrc E0) (asmLen E0) s := by
      rw [show asmLen E0 = 0 from E0_asmLen]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [CopyPre, E0_asmDst, E0_asmSrc, E0_W]
    obtain ⟨k, s', hk, hstep, hpc', hp⟩ := h s hpc ⟨hCopyPre, hs.2.1, hs.2.2.1⟩
    have hk' : (k : ℝ) ≤ 14 := by simpa using hk
    exact ⟨k, s', hk', hstep, hpc', hp.1, hp.2.2,
      dstZero_of_wordsOf_zero (by rw [wordsOf_zero]) s'⟩
  · -- `res`: the real `Sres`, with the trivial sketch subroutine
    intro pref
    have hsk : StageRun (progDecOfTop (.code []) (.code []) (.code []) SassemP
        (SresP (.code []) 12 0) (.code [])) E0
        (dResBase (.code []) (.code []) (.code []) SassemP)
        (dResBase (.code []) (.code []) (.code []) SassemP + (Stmt.code []).len) 0
        (fun s => HoldsVec E0.W 0 (resSrc E0) s (setVec 0 Aset) ∧
          HoldsVecPad E0.W 0 (asmDst E0) s (asmVec E0.W 0 pref) ∧ DstZero E0 0 s)
        (fun s => HoldsVec E0.W 0 (resDst E0) s (setVec 0 Bset) ∧
          HoldsVec E0.W 0 (resSrc E0) s (setVec 0 Aset) ∧
          HoldsVecPad E0.W 0 (asmDst E0) s (asmVec E0.W 0 pref)) := by
      intro s hpc hpre
      refine ⟨0, s, ?_, rfl, ?_, ?_, hpre.1, hpre.2.1⟩
      · norm_num
      · rw [hpc]; simp [Stmt.len]
      · intro j hj
        rw [wordsOf_zero] at hj
        omega
    have h := stageRun_resP (Sini := (.code [])) (Srow := (.code [])) (Sdec := (.code []))
      (Sassem' := SassemP) (Scr := (.code [])) (Ssketch := (.code [])) (E := E0) (M := 0) (m := 0)
      (Aset := Aset) (Bset := Bset) (estVec := asmVec E0.W 0 pref) (Tsk := 0)
      (by norm_num) (by norm_num) (by norm_num) (by simp) (by simp [wordsOf_zero])
      (by simp) (by simp) (by simp) hsk
    exact (by simpa [DstZero, wordsOf_zero] using h)
  · -- `cr`: the empty CR program, `0` steps, and the output list is empty
    intro pref
    intro s hpc hpre
    have h1 : s.regs 1 = 0 := by
      have h := hpre.1.2.2.1
      simpa [wordsOf_zero] using h
    refine ⟨0, s, ?_, rfl, ?_, ?_⟩
    · norm_num
    · rw [hpc]
      simp [dEnd, dCrBase, dResBase, Stmt.len]
    · show OutListIs s (symmDiff (sch0.assembled lr0 ∅ pref) S)
      rw [hS, sch0_assembled, symmDiff_empty_right]
      refine ⟨?_, ?_⟩
      · have h0 : outList s = [] := by simp [outList, h1]
        rw [h0]
        exact List.nodup_nil
      · intro v
        have h0 : outList s = [] := by simp [outList, h1]
        rw [h0]
        simp

/-- The CR family `cr0` has an additive syndrome (trivially: every syndrome is empty). -/
theorem cr0_sketch_add (A B : Finset ℕ) :
    cr0.sketch sch0.N 0 (symmDiff A B)
      = symmDiff (cr0.sketch sch0.N 0 A) (cr0.sketch sch0.N 0 B) := by
  rw [cr0_sketch, cr0_sketch, cr0_sketch, symmDiff_empty_empty]

/-- **The propagated composition is non-vacuous, and so is its conclusion**: at the model above,
`topDecCorrects_of_stagesZ` applies, and the `TopDecCorrects` it yields holds at the same programs.
(The decoder is the identity: the only halting run is the zero-step one, whose output list is
empty.) -/
theorem stagesZ_model_corrects :
    TopDecCorrects (.code []) (.code []) (.code []) SassemP (SresP (.code []) 12 0) (.code [])
      E0 (fun (_ : Fin sch0.N → ZMod 2) => fun i : Fin 0 => i.elim0) 36 := by
  have h := topDecCorrects_of_stagesZ (Sinit := (.code [])) (Srow := (.code []))
    (Sdec := (.code [])) (Sassem := SassemP) (Sres := SresP (.code []) 12 0) (Scr := (.code []))
    (E := E0) (M := 0) (sch := sch0) (lr := lr0) (J := ∅)
    (D := fun (_ : Fin sch0.N → ZMod 2) => fun i : Fin 0 => i.elim0) (RowOut := fun _ => True)
    (CR := cr0) (t := 0) (Tini := 0) (Trow := 2) (Tdec := 2) (Tas := 14) (Tres := 18) (Tcr := 0)
    (fun A B => cr0_sketch_add A B)
    (fun x => by
      have hS : symmDiff (supp x) (sch0.exactEstimate lr0 (supp x) ∅) = ∅ := by
        rw [sch0_supp, sch0_exactEstimate, symmDiff_empty_empty]
      exact stagesZ_model x (cr0.sketch sch0.N 0 (supp x))
        (cr0.sketch sch0.N 0 (sch0.exactEstimate lr0 (supp x) ∅)) _ hS)
  have hcost : (0 : ℝ) + 2 + 2 + 14 + 18 + 0 = 36 := by norm_num
  rwa [hcost] at h

/-! ### 10.2 The conjunct is not vacuous: an inhabitant with `wordsOf 12 1 = 1` -/

/-- `wordsOf 12 1 = 1`: a one-bit payload occupies exactly one word. -/
theorem wordsOf_twelve_one : wordsOf 12 1 = 1 := by
  norm_num [wordsOf]

/-- **The full `hSk` precondition, inhabited where the payload block is a real word.**  At
`W = 12`, `M = 1`, `Aset = ∅`, `m = 0` and the all-zero memory, all three conjuncts of the
strengthened precondition hold, and `wordsOf 12 1 = 1` (so the `writeArray` conjunct constrains a
non-empty block: it forces `mem 0 = 0`). -/
theorem hSkPre_M1_inhabited :
    ∃ s : RAMState, wordsOf 12 1 = 1 ∧
      HoldsVec 12 1 0 s (setVec 1 (∅ : Finset ℕ)) ∧
      HoldsVecPad 12 0 0 s (asmVec 12 0 (fun i => i.elim0)) ∧
      writeArray 0 s.mem (fun _ => 0) (wordsOf 12 1) = s.mem := by
  refine ⟨⟨0, fun _ => 0, fun _ => 0⟩, wordsOf_twelve_one, ?_, ?_, ?_⟩
  · intro j hj
    have hj' : j < 1 := by rwa [wordsOf_twelve_one] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [HoldsVec, packMem, setVec]
  · intro j hj
    rw [wordsOf_zero] at hj
    omega
  · have h : DstZero E0 1 ⟨0, fun _ => 0, fun _ => 0⟩ := by
      rw [dstZero_iff]
      intro a h1 h2
      rfl
    simpa [DstZero] using h

/-! ### 10.3 The preservation fact at the `SassemP` shape

`SassemP`'s memory effect is `writeArray (asmDst E) m (fun i => m (asmSrc E + i)) (asmLen E)`
(`copyArray_spec`).  The general `dstZero_writeArray` above applies whenever that block is disjoint
from the payload block.  As a corollary in the layout the caller uses (`asmDst E + m ≤ resDst E`),
the assembly's copy preserves the calling convention. -/

/-- **The assembly's copy preserves the zeroed CR payload**, in the layout `asmDst E + m ≤ resDst E`. -/
theorem dstZero_asmCopy {E : RAMEnv} {M m : ℕ} {src : ℕ} {mem : ℕ → ℕ}
    (hsep : asmDst E + m ≤ resDst E)
    (h : writeArray (resDst E) mem (fun _ => 0) (wordsOf E.W M) = mem) :
    writeArray (resDst E) (writeArray (asmDst E) mem (fun i => mem (src + i)) m)
        (fun _ => 0) (wordsOf E.W M)
      = writeArray (asmDst E) mem (fun i => mem (src + i)) m :=
  dstZero_writeArray (f := fun i => mem (src + i)) (Or.inl hsep) h


end C8R
end LinearSetReconciliation327.Main


