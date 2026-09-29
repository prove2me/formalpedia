-- Prove2me | Definitions.Def_NoAdjacentGapEquiv
-- name    : NoAdjacentGapEquiv
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-09-25T17:10:28.937525+00:00
-- url     : https://prove2.me/theorems/afa0e06d-c270-4a4b-934b-eb5e94188d06
-- title:
--   Gap and recurrence equivalences for no-adjacent-one strings
-- statement:
--   Data-level equivalences supporting the counting theorems for binary strings with no adjacent ones, built on Def_NoAdjacentBinaryStrings.
--
--   gapMonoEquiv gives a bijection between GapMono n k (strictly monotone position embeddings with successive gaps at least two) and strictly monotone tuples Fin k → Fin (n+1-k): the forward map subtracts each selected position's index, and the inverse adds it.
--
--   strictMonoCardEquiv gives a bijection between strictly monotone tuples Fin k → Fin m and the k-element finsets of Fin m.
--
--   noAdjacentFinsetCardEquiv gives a bijection between exact-k no-adjacent finsets of Fin n and GapMono n k.
--
--   noAdjacentStringsRecurrenceEquiv expresses the Fibonacci recurrence as a bijection: a valid length-(n+2) string either ends in 0 (its prefix is any valid length-(n+1) string) or in 01 (its prefix is any valid length-n string).
--
--   Auxiliary lemmas needed to construct these equivalences are included: chain-gap estimates, the lower bound g i ≥ 2 i for gap-2 tuples, and closure of the no-adjacent property under Fin.init and Fin.snoc with appended 0 or 01.
-- source:
--   Kenneth H. Rosen, Discrete Mathematics and Its Applications, 8th ed., Chapter 6 and Section 8.1: gap bijections for binary strings with no consecutive 1s.

import Definitions.Def_NoAdjacentBinaryStrings
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sort

/-!
# Gap-compression and recurrence equivalences for no-adjacent-one strings

This file is the data-level infrastructure supporting the counting theorems for
binary strings with no adjacent ones. It is built on `Def_NoAdjacentBinaryStrings`
and provides three equivalences together with the auxiliary lemmas used to construct
them:

* `gapMonoEquiv` — gap-2 monotone position tuples `GapMono n k` are in bijection with
  arbitrary strictly monotone tuples `Fin k → Fin (n+1-k)`;
* `strictMonoCardEquiv` — strictly monotone tuples `Fin k → Fin m` are in bijection with
  the `k`-element finsets of `Fin m`;
* `noAdjacentFinsetCardEquiv` — exact-`k` no-adjacent finsets are in bijection with
  `GapMono n k`;
* `noAdjacentStringsRecurrenceEquiv` — splitting a length-`n+2` string on its last bit
  gives the Fibonacci recurrence as a bijection with a disjoint sum.
-/

open Finset Function

namespace NoAdjString

/-! ## Membership helpers -/

/-- A string with no adjacent ones belongs to `noAdjacentStrings`. -/
lemma in_noAdjacentStrings {n : ℕ} {f : Fin n → Bool} (hf : NoAdjacentOnes f) :
    f ∈ noAdjacentStrings n := by
  classical
  simp [noAdjacentStrings, hf]

/-- Membership in `noAdjacentStrings n` is equivalent to `NoAdjacentOnes f`. -/
lemma mem_noAdjacentStrings_iff {n : ℕ} {f : Fin n → Bool} :
    f ∈ noAdjacentStrings n ↔ NoAdjacentOnes f := by
  classical
  simp [noAdjacentStrings]

/-- Membership in the finset exact-`k` family is equivalent to the conjunction of
the no-adjacent property and cardinality `k`. -/
lemma mem_noAdjacentFinsetCard_iff {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ noAdjacentFinsetCard n k ↔ s.noAdjacent ∧ s.card = k := by
  simp [noAdjacentFinsetCard, noAdjacentFinset]

/-! ## Helper lemmas -/

/-- Chain lemma for a gap-2 tuple. -/
lemma gap_chain_ge {n k : ℕ} (g : Fin k → Fin n)
    (hg : ∀ (i : Fin k) (h : i.val + 1 < k), (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2)
    (i j : ℕ) (hi : i < k) (hij : i + j < k) :
    (g ⟨i + j, hij⟩).val ≥ (g ⟨i, hi⟩).val + 2 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h5 : i + j < k := by omega
    have h6 : i + j + 1 < k := by omega
    have hstep : (g ⟨i + j + 1, h6⟩).val ≥ (g ⟨i + j, h5⟩).val + 2 := hg ⟨i + j, h5⟩ h6
    have ih' : (g ⟨i + j, h5⟩).val ≥ (g ⟨i, hi⟩).val + 2 * j := ih h5
    calc
      (g ⟨i + j + 1, h6⟩).val ≥ (g ⟨i + j, h5⟩).val + 2 := hstep
      _ ≥ (g ⟨i, hi⟩).val + 2 * j + 2 := by omega

/-- A gap-2 tuple satisfies `(g i).val ≥ 2 * i.val`. -/
lemma gap_g_ge_two {n k : ℕ} (g : Fin k → Fin n)
    (hg : ∀ (i : Fin k) (h : i.val + 1 < k), (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2)
    (i : Fin k) : (g i).val ≥ 2 * i.val := by
  have h_main : ∀ (j : ℕ) (hj : j < k), (g ⟨j, hj⟩).val ≥ 2 * j := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hprev : j < k := by omega
      have hstep : (g ⟨j + 1, hj⟩).val ≥ (g ⟨j, hprev⟩).val + 2 := hg ⟨j, hprev⟩ hj
      have ihv : (g ⟨j, hprev⟩).val ≥ 2 * j := ih hprev
      calc
        (g ⟨j + 1, hj⟩).val ≥ (g ⟨j, hprev⟩).val + 2 := hstep
        _ ≥ 2 * j + 2 := by linarith
        _ = 2 * (j + 1) := by ring
  have h_final := h_main i.val i.is_lt
  have h_eq : (⟨i.val, i.is_lt⟩ : Fin k) = i := by
    apply Fin.ext
    simp
  rw [h_eq] at h_final
  exact h_final

/-- A strictly monotone function out of `Fin k` satisfies `(f i).val ≥ i.val`. -/
lemma strictMono_ge_val {m k : ℕ} (f : Fin k → Fin m) (hf : StrictMono f)
    (i : Fin k) : (f i).val ≥ i.val := by
  have h_main : ∀ (j : ℕ) (hj : j < k), (f ⟨j, hj⟩).val ≥ j := by
    intro j
    induction j with
    | zero => intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hprev : j < k := by omega
      have hnat : j < j + 1 := by omega
      have hlt : (⟨j, hprev⟩ : Fin k) < ⟨j + 1, hj⟩ := by exact?
      have hstep : f ⟨j, hprev⟩ < f ⟨j + 1, hj⟩ := hf hlt
      have hstep' : (f ⟨j + 1, hj⟩).val ≥ (f ⟨j, hprev⟩).val + 1 :=
        Nat.add_one_le_iff.mpr hstep
      have ihv : (f ⟨j, hprev⟩).val ≥ j := ih hprev
      calc
        (f ⟨j + 1, hj⟩).val ≥ (f ⟨j, hprev⟩).val + 1 := hstep'
        _ ≥ j + 1 := by linarith
  have h_final := h_main i.val i.is_lt
  have h_eq : (⟨i.val, i.is_lt⟩ : Fin k) = i := by
    apply Fin.ext
    simp
  rw [h_eq] at h_final
  exact h_final

/-! ## gap compression -/

/-- Forward map: subtract the index of each selected position. -/
def gapCompress (n k : ℕ) (x : GapMono n k) : Fin k → Fin (n + 1 - k) := fun i =>
  let g : Fin k ↪ Fin n := x.val
  let hg := x.property
  let gfun : Fin k → Fin n := g
  have hg' : ∀ (i : Fin k) (h : i.val + 1 < k),
      (gfun ⟨i.val + 1, h⟩).val ≥ (gfun i).val + 2 := hg
  let d : ℕ := k - 1 - i.val
  have hkpos : 0 < k := Fin.pos i
  have hsum : i.val + d = k - 1 := by omega
  have hlt_top : i.val + d < k := by
    have : i.val + d = k - 1 := hsum
    omega
  have hchain0 := gap_chain_ge gfun hg' i.val d i.is_lt hlt_top
  have hchain : (gfun ⟨k - 1, by omega⟩).val ≥ (gfun i).val + 2 * d := by
    have heq : (⟨i.val + d, hlt_top⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
      apply Fin.ext
      omega
    rw [heq] at hchain0
    exact hchain0
  have hlast : (gfun ⟨k - 1, by omega⟩).val ≤ n - 1 :=
    Nat.le_sub_one_of_lt (gfun _).is_lt
  have h9 : (gfun i).val + 2 * d ≤ n - 1 := hchain.trans hlast
  have h10 : (gfun i).val ≤ (n - 1) - 2 * d := by
    have h11 : 2 * d ≤ n - 1 := by omega
    omega
  have hgei : (gfun i).val ≥ i.val := by
    have h12 := gap_g_ge_two gfun hg' i
    omega
  have h14 : (gfun i).val - i.val < n + 1 - k := by omega
  ⟨(gfun i).val - i.val, h14⟩

/-- The forward map is strictly monotone. -/
lemma gapCompress_strictMono (n k : ℕ) (x : GapMono n k) :
    StrictMono (gapCompress n k x) := fun i j hlt => by
  let g : Fin k ↪ Fin n := x.val
  let hg := x.property
  let gfun : Fin k → Fin n := g
  have hg' : ∀ (i : Fin k) (h : i.val + 1 < k),
      (gfun ⟨i.val + 1, h⟩).val ≥ (gfun i).val + 2 := hg
  set d : ℕ := j.val - i.val with hd
  have hjd : i.val + d = j.val := by omega
  have hchain0 := gap_chain_ge gfun hg' i.val d i.is_lt (by omega)
  have hchain : (gfun j).val ≥ (gfun i).val + 2 * d := by
    have heq : (⟨i.val + d, by omega⟩ : Fin k) = j := by
      apply Fin.ext
      omega
    rw [heq] at hchain0
    exact hchain0
  have hgei : (gfun i).val ≥ i.val := by
    have h12 := gap_g_ge_two gfun hg' i
    omega
  have hgej : (gfun j).val ≥ j.val := by omega
  have hgoal : (gfun j).val - j.val > (gfun i).val - i.val := by omega
  simpa [gapCompress] using hgoal

/-- Inverse map: add the index of each selected position. -/
def gapExpand (n k : ℕ) (f : Fin k → Fin (n + 1 - k)) (hf : StrictMono f) :
    Fin k → Fin n := fun i =>
  have hge : ∀ (j : Fin k), (f j).val ≥ j.val := strictMono_ge_val f hf
  have hle : k ≤ n + 1 - k := by
    by_cases hk : k = 0
    · omega
    · have h1 : (f ⟨k - 1, by omega⟩).val ≥ k - 1 := hge ⟨k - 1, by omega⟩
      have h3 : (f ⟨k - 1, by omega⟩).val < n + 1 - k := (f _).is_lt
      omega
  have hfi0 : (f i).val ≤ (n + 1 - k) - 1 := Nat.le_sub_one_of_lt (f i).is_lt
  have hfi : (f i).val ≤ n - k := by omega
  have h9 : i.val ≤ k - 1 := by omega
  have h10 : (f i).val + i.val ≤ n - 1 := by
    calc
      (f i).val + i.val ≤ (n - k) + i.val := by gcongr
      _ ≤ n - 1 := by omega
  have hnpos : 0 < n := by omega
  have h12 : (f i).val + i.val + 1 ≤ n := by
    have h13 : (f i).val + i.val ≤ n - 1 := h10
    have h14 : (n - 1) + 1 = n := by omega
    omega
  have h11 : (f i).val + i.val < n := Nat.lt_of_succ_le h12
  ⟨(f i).val + i.val, h11⟩

/-- The inverse map is strictly monotone. -/
lemma gapExpand_strictMono (n k : ℕ) (f : Fin k → Fin (n + 1 - k)) (hf : StrictMono f) :
    StrictMono (gapExpand n k f hf) := fun i j hlt => by
  have hstep : f i < f j := hf hlt
  have h10 : (f j).val ≥ (f i).val + 1 := Nat.add_one_le_iff.mpr hstep
  have h11 : j.val ≥ i.val + 1 := by omega
  have h12 : (f j).val + j.val ≥ (f i).val + i.val + 1 := by omega
  have hlt2 : (⟨(f i).val + i.val, by omega⟩ : Fin n) <
      ⟨(f j).val + j.val, by omega⟩ := by exact?
  simpa [gapExpand] using hlt2

/-- The inverse map has gaps at least two. -/
lemma gapExpand_gap (n k : ℕ) (f : Fin k → Fin (n + 1 - k)) (hf : StrictMono f)
    (i : Fin k) (h : i.val + 1 < k) :
    (gapExpand n k f hf ⟨i.val + 1, h⟩).val ≥ (gapExpand n k f hf i).val + 2 := by
  have hnat : i.val < i.val + 1 := by omega
  have hlt : (i : Fin k) < ⟨i.val + 1, h⟩ := by exact?
  have h2 : (f ⟨i.val + 1, h⟩).val ≥ (f i).val + 1 :=
    Nat.add_one_le_iff.mpr (hf hlt)
  have h_a : (gapExpand n k f hf ⟨i.val + 1, h⟩).val =
      (f ⟨i.val + 1, h⟩).val + (i.val + 1) := rfl
  have h_b : (gapExpand n k f hf i).val = (f i).val + i.val := rfl
  rw [h_a, h_b]
  calc
    (f ⟨i.val + 1, h⟩).val + (i.val + 1)
      ≥ ((f i).val + 1) + (i.val + 1) := by gcongr
    _ = (f i).val + i.val + 2 := by omega

/-- The gap compression equivalence. -/
def gapMonoEquiv (n k : ℕ) :
    GapMono n k ≃ {f : Fin k → Fin (n + 1 - k) // StrictMono f} :=
  let fwd (x : GapMono n k) : {f // StrictMono f} :=
    ⟨gapCompress n k x, gapCompress_strictMono n k x⟩
  let inv (x : {f // StrictMono f}) : GapMono n k :=
    let f := x.val
    let hf := x.2
    let g : Fin k → Fin n := gapExpand n k f hf
    have hsm : StrictMono g := gapExpand_strictMono n k f hf
    let g' : Fin k ↪ Fin n := ⟨g, hsm.injective⟩
    have hg : ∀ (i : Fin k) (h : i.val + 1 < k),
        (g' ⟨i.val + 1, h⟩).val ≥ (g' i).val + 2 := gapExpand_gap n k f hf
    ⟨g', hg⟩
  have hleft : ∀ x, inv (fwd x) = x := by
    intro x
    have h : (inv (fwd x)).val = x.val := by
      ext i
      dsimp only [inv, fwd]
      let f : Fin k → Fin (n + 1 - k) := gapCompress n k x
      have hfm : StrictMono f := gapCompress_strictMono n k x
      show (gapExpand n k f hfm i).val = (x.val i).val
      have hv1 : (gapExpand n k f hfm i).val = (f i).val + i.val := rfl
      have hv2 : (f i).val = (x.val i).val - i.val := rfl
      rw [hv1, hv2]
      have hge : (x.val i).val ≥ i.val := by
        have h12 := gap_g_ge_two x.val x.property i
        omega
      omega
    exact Subtype.ext h
  have h_all : ∀ (e' : {f : Fin k → Fin (n + 1 - k) // StrictMono f}) (i : Fin k),
      (gapCompress n k (inv e') i).val = (e'.val i).val := by
    intro e' i
    dsimp only [inv]
    let gemb : Fin k ↪ Fin n :=
      ⟨gapExpand n k e'.val e'.2,
        (gapExpand_strictMono n k e'.val e'.2).injective⟩
    show (gemb i).val - i.val = (e'.val i).val
    have h1 : (gemb i).val = (e'.val i).val + i.val := rfl
    rw [h1]
    omega
  have hright : ∀ x, fwd (inv x) = x := by
    intro x
    have h : (fwd (inv x)).val = x.val := by
      funext i
      dsimp only [fwd]
      exact Fin.ext (h_all x i)
    exact Subtype.ext h
  { toFun := fwd, invFun := inv, left_inv := hleft, right_inv := hright }

/-! ## strictly monotone functions vs k-element finsets -/

/-- Strictly monotone functions `Fin k → Fin m` are in bijection with the
`k`-element finsets of `Fin m`. -/
def strictMonoCardEquiv (m k : ℕ) :
    {f : Fin k → Fin m // StrictMono f} ≃ {s : Finset (Fin m) // s.card = k} :=
  let fwd2 (x : {f // StrictMono f}) : {s : Finset (Fin m) // s.card = k} :=
    have hc : (Finset.image x.val Finset.univ).card = k := by
      rw [Finset.card_image_of_injective _ x.2.injective, Finset.card_univ,
        Fintype.card_fin]
    ⟨Finset.image x.val Finset.univ, hc⟩
  let inv2 (x : {s // s.card = k}) : {f // StrictMono f} :=
    let e : Fin k ↪o Fin m := Finset.orderEmbOfFin x.1 x.2
    ⟨(e : Fin k → Fin m), e.strictMono⟩
  have hleft : ∀ x, inv2 (fwd2 x) = x := by
    intro x
    let oe : Fin k ↪o Fin m := OrderEmbedding.ofStrictMono x.val x.2
    let s0 : Finset (Fin m) := Finset.image x.val Finset.univ
    have hcs : s0.card = k := by
      rw [Finset.card_image_of_injective _ x.2.injective, Finset.card_univ,
        Fintype.card_fin]
    let e1 : Fin k ↪o Fin m := Finset.orderEmbOfFin s0 hcs
    have hr1 : Set.range e1 = (s0 : Set (Fin m)) := Finset.range_orderEmbOfFin s0 hcs
    have h2 : Set.range x.val = (s0 : Set (Fin m)) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩)
      · intro hy
        have : y ∈ Finset.image x.val Finset.univ := Finset.mem_coe.mp hy
        rcases Finset.mem_image.mp this with ⟨z, _, rfl⟩
        exact ⟨z, rfl⟩
    have hr2 : Set.range oe = (s0 : Set (Fin m)) := by
      have h : Set.range oe = Set.range x.val := rfl
      exact h.trans h2
    have h_eq : e1 = oe := (OrderEmbedding.range_inj).mp (hr1.trans hr2.symm)
    have h3 : (e1 : Fin k → Fin m) = x.val := by
      rw [h_eq]
      rfl
    dsimp only [inv2, fwd2]
    exact Subtype.ext h3
  have hright : ∀ x, fwd2 (inv2 x) = x := by
    intro x
    dsimp only [fwd2, inv2]
    exact Subtype.ext (Finset.image_orderEmbOfFin_univ x.val x.2)
  { toFun := fwd2, invFun := inv2,
    left_inv := fun x => hleft x, right_inv := fun x => hright x }

/-- A gap-2 embedding is strictly monotone. -/
lemma gapMono_strictMono {n k : ℕ} (g : Fin k ↪ Fin n)
    (hg : ∀ (i : Fin k) (h : i.val + 1 < k),
      (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2) :
    StrictMono g := by
  intro a b h
  let d : ℕ := b.val - a.val
  have hpos : 0 < d := by omega
  have hsum : a.val + d = b.val := by omega
  have hchain0 := gap_chain_ge g hg a.val d a.is_lt (by omega)
  have heq : (⟨a.val + d, by omega⟩ : Fin k) = b := by
    apply Fin.ext; exact hsum
  rw [heq] at hchain0
  have hnat : (g b).val ≥ (g a).val + 2 * d := hchain0
  have hlt : (g a).val < (g b).val := by omega
  exact?

/-! ## exact-k no-adjacent finsets vs GapMono -/

/-- Exact-`k` no-adjacent finsets of `Fin n` are in bijection with
`GapMono n k`. -/
def noAdjacentFinsetCardEquiv (n k : ℕ) :
    {s : Finset (Fin n) // s ∈ noAdjacentFinsetCard n k} ≃ GapMono n k :=
  let fwd (x : {s // s ∈ noAdjacentFinsetCard n k}) : GapMono n k :=
    let s := x.val
    have hmem : s.noAdjacent ∧ s.card = k :=
      (mem_noAdjacentFinsetCard_iff.mp x.2)
    let hna := hmem.1
    let hk := hmem.2
    let oe : Fin k ↪o Fin n := Finset.orderEmbOfFin s hk
    let g : Fin k ↪ Fin n := oe.toEmbedding
    have hrange : ∀ (t : Fin k), g t ∈ s := by
      intro t
      have h5 : g t ∈ Set.range (oe : Fin k → Fin n) := ⟨t, rfl⟩
      rw [Finset.range_orderEmbOfFin s hk] at h5
      exact Finset.mem_coe.mp h5
    have hgap : ∀ (i : Fin k) (h : i.val + 1 < k),
        (g ⟨i.val + 1, h⟩).val ≥ (g i).val + 2 := by
      intro i h
      have hnat : i.val < i.val + 1 := by omega
      have hlt : (i : Fin k) < ⟨i.val + 1, h⟩ := by exact?
      have h1 : g i < g ⟨i.val + 1, h⟩ := oe.strictMono hlt
      have hgi : g i ∈ s := hrange i
      by_contra h2
      have h3 : (g ⟨i.val + 1, h⟩).val = (g i).val + 1 := by omega
      have hb : g ⟨i.val + 1, h⟩ = ⟨(g i).val + 1, by omega⟩ := by
        apply Fin.ext; exact h3
      have hgj : g ⟨i.val + 1, h⟩ ∈ s := hrange ⟨i.val + 1, h⟩
      have h4 : ⟨(g i).val + 1, _⟩ ∈ s := hb ▸ hgj
      exact hna (g i) hgi (by omega) h4
    ⟨g, hgap⟩
  let inv (y : GapMono n k) : {s // s ∈ noAdjacentFinsetCard n k} :=
    let g : Fin k ↪ Fin n := y.val
    let s : Finset (Fin n) := Finset.image g Finset.univ
    have hk : s.card = k := by
      rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ,
        Fintype.card_fin]
    have hsm : StrictMono g := gapMono_strictMono g y.property
    have hna : s.noAdjacent := by
      intro x hx hnext
      rw [Finset.mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      intro hbad
      rw [Finset.mem_image] at hbad
      rcases hbad with ⟨j, _, hj⟩
      have hne : j ≠ i := by
        intro h
        rw [h] at hj
        have h9 : (g i).val = (g i).val + 1 := congr_arg Fin.val hj
        omega
      have hlt : i < j := by
        by_cases h : i < j
        · exact h
        · have hji : j < i := by omega
          let d2 : ℕ := i.val - j.val
          have hsum2 : j.val + d2 = i.val := by omega
          have hchain0 := gap_chain_ge g y.property j.val d2 j.is_lt (by omega)
          have heq : (⟨j.val + d2, by omega⟩ : Fin k) = i := by
            apply Fin.ext; exact hsum2
          rw [heq] at hchain0
          have hc : (g i).val ≥ (g j).val + 2 * d2 := hchain0
          rw [hj] at hc
          simp at hc
          omega
      let d : ℕ := j.val - i.val
      have hpos : 0 < d := by omega
      have hsum : i.val + d = j.val := by omega
      have hchain0 := gap_chain_ge g y.property i.val d i.is_lt (by omega)
      have heq : (⟨i.val + d, by omega⟩ : Fin k) = j := by
        apply Fin.ext; exact hsum
      rw [heq] at hchain0
      have hc : (g j).val ≥ (g i).val + 2 * d := hchain0
      rw [hj] at hc
      simp at hc
      omega
    have hmem : s ∈ noAdjacentFinsetCard n k :=
      mem_noAdjacentFinsetCard_iff.mpr ⟨hna, hk⟩
    ⟨s, hmem⟩
  have hleft : ∀ x, inv (fwd x) = x := by
    intro x
    let s := x.val
    have hmem : s.noAdjacent ∧ s.card = k := mem_noAdjacentFinsetCard_iff.mp x.2
    have hk := hmem.2
    dsimp only [inv, fwd]
    have h : Finset.image (Finset.orderEmbOfFin s hk) Finset.univ = s :=
      Finset.image_orderEmbOfFin_univ s hk
    exact Subtype.ext h
  have hright : ∀ y, fwd (inv y) = y := by
    intro y
    let g : Fin k ↪ Fin n := y.val
    let s : Finset (Fin n) := Finset.image g Finset.univ
    have hk : s.card = k := by
      rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ,
        Fintype.card_fin]
    have hsm : StrictMono g := gapMono_strictMono g y.property
    let oe : Fin k ↪o Fin n := Finset.orderEmbOfFin s hk
    let og : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono g hsm
    have h1 : Set.range (oe : Fin k → Fin n) = (s : Set (Fin n)) :=
      Finset.range_orderEmbOfFin s hk
    have h2 : Set.range (og : Fin k → Fin n) = Set.range g := rfl
    have h3 : Set.range g = (s : Set (Fin n)) := by
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)
      · intro hz
        have : z ∈ s := Finset.mem_coe.mp hz
        rcases Finset.mem_image.mp this with ⟨t, _, rfl⟩
        exact ⟨t, rfl⟩
    have h4 : oe = og := OrderEmbedding.range_inj.mp
      (h1.trans ((h2.trans h3).symm))
    have h5 : oe.toEmbedding = g := by
      rw [h4]; rfl
    dsimp only [fwd, inv]
    exact Subtype.ext h5
  { toFun := fwd, invFun := inv,
    left_inv := fun x => hleft x, right_inv := fun x => hright x }

/-! ## The Fibonacci recurrence bijection -/

/-- Restricting a no-adjacent string with last bit `false` gives a valid
prefix. -/
lemma noAdjacent_init {m : ℕ} {f : Fin (m + 1) → Bool} (hf : NoAdjacentOnes f) :
    NoAdjacentOnes (Fin.init f) := by
  intro i h
  have h1 : Fin.init f i = f i.castSucc := by simp [Fin.init]
  have h2 : Fin.init f ⟨i.val + 1, h⟩ = f (Fin.castSucc ⟨i.val + 1, h⟩) := by
    simp [Fin.init]
  rw [h1, h2]
  have h' : i.val + 1 < m + 1 := by linarith
  exact hf i.castSucc h'

/-- Appending `false` to a valid string gives a valid string. -/
lemma noAdjacent_snoc_false {m : ℕ} {g : Fin m → Bool} (hg : NoAdjacentOnes g) :
    NoAdjacentOnes (Fin.snoc g false) := by
  let f' : Fin (m + 1) → Bool := Fin.snoc g false
  have hval : ∀ (x : Fin (m + 1)) (hx : x.val < m), f' x = g ⟨x.val, hx⟩ := by
    intro x hx
    have h5 : ∀ (y : Fin m), f' y.castSucc = g y := fun y =>
      Fin.snoc_castSucc (α := fun _ => Bool) false g y
    have h6 := h5 ⟨x.val, hx⟩
    convert h6
    apply Fin.ext; simp
  have hlast : f' (Fin.last m) = false := by
    simp [f']
  have hff : NoAdjacentOnes f' := by
    intro i h
    have h_i_lt : i.val < m := by omega
    have h1 : f' i = g ⟨i.val, h_i_lt⟩ := hval i h_i_lt
    by_cases h10 : i.val + 1 < m
    · have h2 : f' ⟨i.val + 1, h⟩ = g ⟨i.val + 1, h10⟩ :=
        hval ⟨i.val + 1, h⟩ h10
      rw [h1, h2]; exact hg ⟨i.val, h_i_lt⟩ h10
    · have heq : (⟨i.val + 1, h⟩ : Fin (m + 1)) = Fin.last m := by
        apply Fin.ext; linarith
      have h2 : f' ⟨i.val + 1, h⟩ = false := by
        rw [heq]; exact hlast
      rw [h1, h2]; simp
  exact hff

/-- Appending `01` to a valid string gives a valid string. -/
lemma noAdjacent_snoc_false_true {m : ℕ} {h : Fin m → Bool} (hh : NoAdjacentOnes h) :
    NoAdjacentOnes (Fin.snoc (Fin.snoc h false) true) := by
  let g1 : Fin (m + 1) → Bool := Fin.snoc h false
  let f' : Fin (m + 2) → Bool := Fin.snoc g1 true
  have hg1val : ∀ (x : Fin (m + 1)) (hx : x.val < m), g1 x = h ⟨x.val, hx⟩ := by
    intro x hx
    have h5 : ∀ (y : Fin m), g1 y.castSucc = h y := fun y =>
      Fin.snoc_castSucc (α := fun _ => Bool) false h y
    have h6 := h5 ⟨x.val, hx⟩
    convert h6
    apply Fin.ext; simp
  have hg1last : g1 (Fin.last m) = false := by
    simp [g1]
  have hval : ∀ (x : Fin (m + 2)) (hx : x.val < m + 1), f' x = g1 ⟨x.val, hx⟩ := by
    intro x hx
    have h5 : ∀ (y : Fin (m + 1)), f' y.castSucc = g1 y := fun y =>
      Fin.snoc_castSucc (α := fun _ => Bool) true g1 y
    have h6 := h5 ⟨x.val, hx⟩
    convert h6
    apply Fin.ext; simp
  have hflast : f' (Fin.last (m + 1)) = true := by
    simp [f']
  have hff : NoAdjacentOnes f' := by
    intro i hgt
    by_cases h9 : i.val < m
    · have h_i_lt1 : i.val < m + 1 := by omega
      have h1 : f' i = h ⟨i.val, h9⟩ := by
        have ha : f' i = g1 ⟨i.val, h_i_lt1⟩ := hval i h_i_lt1
        rw [ha, hg1val ⟨i.val, by omega⟩ h9]
      by_cases h10 : i.val + 1 < m
      · have hnext_lt : i.val + 1 < m + 1 := by omega
        have h2 : f' ⟨i.val + 1, hgt⟩ = h ⟨i.val + 1, h10⟩ := by
          have hb : f' ⟨i.val + 1, hgt⟩ = g1 ⟨i.val + 1, hnext_lt⟩ :=
            hval ⟨i.val + 1, hgt⟩ hnext_lt
          rw [hb, hg1val ⟨i.val + 1, by omega⟩ h10]
        rw [h1, h2]; exact hh ⟨i.val, h9⟩ h10
      · -- i.val + 1 = m: the next position is the appended `false`
        have h11 : i.val + 1 ≥ m := Nat.le_of_not_lt h10
        have h12 : i.val + 1 ≤ m := by linarith
        have h13 : i.val + 1 = m := le_antisymm h12 h11
        have h_eqv : (⟨i.val + 1, hgt⟩ : Fin (m + 2)) =
            (Fin.last m).castSucc := by
          apply Fin.ext
          exact h13
        have h2 : f' ⟨i.val + 1, hgt⟩ = false := by
          rw [h_eqv]
          have hc : f' ((Fin.last m).castSucc) = g1 (Fin.last m) := by
            simp [f']
          rw [hc, hg1last]
        rw [h1, h2]; simp
    · -- i.val ≥ m; hgt forces i.val = m (pair false, true)
      have him : i.val = m := by omega
      have h1 : f' i = false := by
        have heq : i = (Fin.last m).castSucc := by
          apply Fin.ext; simp [him]
        rw [heq]
        have hc : f' ((Fin.last m).castSucc) = g1 (Fin.last m) := by
          simp [f']
        rw [hc, hg1last]
      have hln : (⟨i.val + 1, hgt⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
        apply Fin.ext; simp [him]
      have h2 : f' ⟨i.val + 1, hgt⟩ = true := by
        rw [hln]; exact hflast
      rw [h1, h2]; simp
  exact hff

/-- Forward direction: classify a length-`n+2` string by its last bit. -/
def fwd12 (n : ℕ) (x : {f : Fin (n + 2) → Bool // f ∈ noAdjacentStrings (n + 2)}) :
    ({g : Fin (n + 1) → Bool // g ∈ noAdjacentStrings (n + 1)} ⊕
     {h : Fin n → Bool // h ∈ noAdjacentStrings n}) :=
  let f := x.val
  have hf : NoAdjacentOnes f := mem_noAdjacentStrings_iff.mp x.2
  if hlast : f (Fin.last (n + 1)) then
    have h1 : ¬ (f ⟨n, by linarith⟩ ∧ f (Fin.last (n + 1))) :=
      hf ⟨n, by linarith⟩ (by linarith)
    have hn_false : f ⟨n, by linarith⟩ = false := by
      simp [hlast] at h1; exact h1
    let h : Fin n → Bool := Fin.init (Fin.init f)
    have hh1 : NoAdjacentOnes (Fin.init f) := noAdjacent_init hf
    have hh : NoAdjacentOnes h := noAdjacent_init hh1
    Sum.inr ⟨h, in_noAdjacentStrings hh⟩
  else
    have hlast' : f (Fin.last (n + 1)) = false := by simpa using hlast
    let g : Fin (n + 1) → Bool := Fin.init f
    have hg : NoAdjacentOnes g := noAdjacent_init hf
    Sum.inl ⟨g, in_noAdjacentStrings hg⟩

/-- Inverse direction: append `0` or `01`. -/
def inv12 (n : ℕ)
    (x : ({g : Fin (n + 1) → Bool // g ∈ noAdjacentStrings (n + 1)} ⊕
          {h : Fin n → Bool // h ∈ noAdjacentStrings n})) :
    {f : Fin (n + 2) → Bool // f ∈ noAdjacentStrings (n + 2)} :=
  match x with
  | Sum.inl (y : {g // g ∈ noAdjacentStrings (n + 1)}) =>
    let g := y.val
    have hg : NoAdjacentOnes g := mem_noAdjacentStrings_iff.mp y.2
    let f : Fin (n + 2) → Bool := Fin.snoc g false
    have hf : NoAdjacentOnes f := noAdjacent_snoc_false hg
    ⟨f, in_noAdjacentStrings hf⟩
  | Sum.inr (z : {h // h ∈ noAdjacentStrings n}) =>
    let h := z.val
    have hh : NoAdjacentOnes h := mem_noAdjacentStrings_iff.mp z.2
    let f : Fin (n + 2) → Bool := Fin.snoc (Fin.snoc h false) true
    have hf : NoAdjacentOnes f := noAdjacent_snoc_false_true hh
    ⟨f, in_noAdjacentStrings hf⟩

/-- Splitting on the last bit gives a disjoint union recurrence. -/
def noAdjacentStringsRecurrenceEquiv (n : ℕ) :
    {f : Fin (n + 2) → Bool // f ∈ noAdjacentStrings (n + 2)} ≃
    ({g : Fin (n + 1) → Bool // g ∈ noAdjacentStrings (n + 1)} ⊕
     {h : Fin n → Bool // h ∈ noAdjacentStrings n}) :=
  have hleft : ∀ x, inv12 n (fwd12 n x) = x := fun x => by
    let f := x.val
    have hf : NoAdjacentOnes f := mem_noAdjacentStrings_iff.mp x.2
    by_cases hlast : f (Fin.last (n + 1))
    · have h1 : ¬ (f ⟨n, by linarith⟩ ∧ f (Fin.last (n + 1))) :=
        hf ⟨n, by linarith⟩ (by linarith)
      have hn_false : f ⟨n, by linarith⟩ = false := by
        simp [hlast] at h1; exact h1
      let h : Fin n → Bool := Fin.init (Fin.init f)
      have hh1 : NoAdjacentOnes (Fin.init f) := noAdjacent_init hf
      have hh : NoAdjacentOnes h := noAdjacent_init hh1
      have hfwd : fwd12 n x = Sum.inr ⟨h, in_noAdjacentStrings hh⟩ := by
        dsimp only [fwd12]
        rw [dif_pos hlast]
      rw [hfwd]
      have h2' : Fin.snoc h false = Fin.init f := by
        rw [←hn_false]; exact Fin.snoc_init_self (Fin.init f)
      have h1' : Fin.snoc (Fin.init f) true = f := by
        have h := Fin.snoc_init_self f
        rw [hlast] at h; exact h
      have hval : (inv12 n (Sum.inr ⟨h, in_noAdjacentStrings hh⟩)).val = f := by
        dsimp only [inv12]
        rw [h2', h1']
      exact Subtype.ext hval
    · have hlast' : f (Fin.last (n + 1)) = false := by simpa using hlast
      let g : Fin (n + 1) → Bool := Fin.init f
      have hg : NoAdjacentOnes g := noAdjacent_init hf
      have hfwd : fwd12 n x = Sum.inl ⟨g, in_noAdjacentStrings hg⟩ := by
        dsimp only [fwd12]
        rw [dif_neg (by simpa using hlast')]
      rw [hfwd]
      have h_eq : Fin.snoc g false = f := by
        have h := Fin.snoc_init_self f
        rw [hlast'] at h; exact h
      have hval : (inv12 n (Sum.inl ⟨g, in_noAdjacentStrings hg⟩)).val = f := by
        dsimp only [inv12]
        exact h_eq
      exact Subtype.ext hval
  have hright : ∀ x, fwd12 n (inv12 n x) = x := fun x => by
    rcases x with (y | z)
    · let g := y.val
      have hg : NoAdjacentOnes g := mem_noAdjacentStrings_iff.mp y.2
      simp [fwd12, inv12]
    · let h := z.val
      have hh : NoAdjacentOnes h := mem_noAdjacentStrings_iff.mp z.2
      simp [fwd12, inv12]
  { toFun := fwd12 n, invFun := inv12 n,
    left_inv := fun x => hleft x, right_inv := fun x => hright x }

end NoAdjString


