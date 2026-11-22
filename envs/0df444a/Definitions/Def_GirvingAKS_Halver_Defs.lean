-- Prove2me | Definitions.Def_GirvingAKS_Halver_Defs
-- name    : GirvingAKS_Halver_Defs
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:47.439261+00:00
-- url     : https://prove2.me/theorems/e59124f0-d368-4116-b334-4ac484d23474
-- title:
--   AKS sorting networks (Seiferas port) — ε-Halver Theory
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/Defs.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Defines ε-halvers and supporting infrastructure.
--
--   Key definitions:
--
--   - `countOnes`, `sortedVersion`: Boolean sequence sorting infrastructure
--   - `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver`: permutation-based
--
--   halver definitions (AKS Section 3). Uses `rank` from `Fin.lean`.
--
--   - `epsHalverMerge`: iterated halver composition
--   - `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure
--
--   The proof that expanders yield ε-halvers is in `FromExpander.lean`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/Defs.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Sort_Defs
import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Misc_Fin

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/Defs.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # ε-Halver Theory

  Defines ε-halvers and supporting infrastructure.

  Key definitions:
  • `countOnes`, `sortedVersion`: Boolean sequence sorting infrastructure
  • `EpsilonInitialHalved`, `EpsilonHalved`, `IsEpsilonHalver`: permutation-based
    halver definitions (AKS Section 3). Uses `rank` from `Fin.lean`.
  • `epsHalverMerge`: iterated halver composition
  • `IsEpsilonSorted`, `Monotone.bool_pattern`: sortedness infrastructure

  The proof that expanders yield ε-halvers is in `FromExpander.lean`.
-/


section


open Finset BigOperators


/-! **Sorted Version and Counting** -/

/-- Count the number of `true` values in a Boolean sequence. -/
def countOnes {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => v i = true)).card

/-- Count ones is bounded by `n`. -/
lemma countOnes_le {n : ℕ} (v : Fin n → Bool) : countOnes v ≤ n := by
  unfold countOnes
  trans (Finset.univ : Finset (Fin n)).card
  · exact Finset.card_filter_le _ _
  · exact le_of_eq (Finset.card_fin n)

/-- Comparator doesn't affect positions other than `c.i` and `c.j`. -/
lemma comparator_affects_only_compared {n : ℕ} (c : Comparator n) (v : Fin n → Bool) (k : Fin n) :
    k ≠ c.i ∧ k ≠ c.j → c.apply v k = v k := by
  intro ⟨hki, hkj⟩
  unfold Comparator.apply
  split_ifs <;> first | rfl | contradiction

/-- Comparators preserve the count of ones (and zeros). -/
lemma comparator_preserves_countOnes {n : ℕ} (c : Comparator n) (v : Fin n → Bool) :
    countOnes (c.apply v) = countOnes v := by
  unfold countOnes
  set S := ({c.i, c.j} : Finset (Fin n))
  set T := Finset.univ \ S
  have hST : Disjoint S T := Finset.disjoint_sdiff
  have hUnion : S ∪ T = Finset.univ := by simp [S, T, Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have split_new : (Finset.univ.filter (fun i => c.apply v i = true)).card =
      (S.filter (fun i => c.apply v i = true)).card +
      (T.filter (fun i => c.apply v i = true)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hST)]
    congr 1
    rw [← Finset.filter_union, hUnion]
  have split_old : (Finset.univ.filter (fun i => v i = true)).card =
      (S.filter (fun i => v i = true)).card +
      (T.filter (fun i => v i = true)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hST)]
    congr 1
    rw [← Finset.filter_union, hUnion]
  rw [split_new, split_old]
  have hT_eq : (T.filter (fun i => c.apply v i = true)).card =
               (T.filter (fun i => v i = true)).card := by
    congr 1; ext k; simp only [Finset.mem_filter, T, Finset.mem_sdiff, Finset.mem_univ,
      true_and, S, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hk, hval⟩
      have hk' : k ≠ c.i ∧ k ≠ c.j := by push_neg at hk; exact hk
      rw [comparator_affects_only_compared c v k hk'] at hval
      exact ⟨by push_neg; exact hk', hval⟩
    · intro ⟨hk, hval⟩
      have hk' : k ≠ c.i ∧ k ≠ c.j := by push_neg at hk; exact hk
      rw [comparator_affects_only_compared c v k hk']
      exact ⟨by push_neg; exact hk', hval⟩
  rw [hT_eq]
  suffices h : (S.filter (fun i => c.apply v i = true)).card =
               (S.filter (fun i => v i = true)).card by omega
  have hne : c.i ≠ c.j := ne_of_lt c.h
  have filter_pair (p : Fin n → Bool) :
      (S.filter (fun i => p i = true)).card =
      (if p c.i = true then 1 else 0) + (if p c.j = true then 1 else 0) := by
    simp only [S, Finset.filter_insert, Finset.filter_singleton]
    split_ifs with h1 h2
    · simp [Finset.card_pair hne]
    · simp
    · simp
    · simp
  rw [filter_pair, filter_pair]
  cases hvi : v c.i <;> cases hvj : v c.j <;>
    simp (config := { decide := true }) [Comparator.apply, hne.symm, hvi, hvj]

/-- Networks preserve the count of ones by preserving it at each step. -/
lemma network_preserves_countOnes {n : ℕ} (net : ComparatorNetwork n) (v : Fin n → Bool) :
    countOnes (net.exec v) = countOnes v := by
  unfold ComparatorNetwork.exec
  have h_fold : ∀ (cs : List (Comparator n)) (w : Fin n → Bool),
      countOnes (List.foldl (fun acc c => c.apply acc) w cs) = countOnes w := by
    intro cs
    induction cs with
    | nil => intro w; rfl
    | cons c cs' ih =>
      intro w
      simp only [List.foldl_cons]
      rw [ih (c.apply w), comparator_preserves_countOnes]
  exact h_fold net.comparators v

/-- The globally sorted version of a Boolean sequence: all 0s then all 1s.
    The threshold is `n - countOnes v`, so positions `[0, threshold)` are false
    and positions `[threshold, n)` are true. -/
def sortedVersion {n : ℕ} (v : Fin n → Bool) : Fin n → Bool :=
  fun i => decide (n - countOnes v ≤ i.val)

/-- The sorted version is monotone. -/
lemma sortedVersion_monotone {n : ℕ} (v : Fin n → Bool) : Monotone (sortedVersion v) := by
  intro i j hij
  unfold sortedVersion
  by_cases h : n - countOnes v ≤ i.val
  · have hj : n - countOnes v ≤ j.val := le_trans h hij
    rw [decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr hj]
  · push_neg at h
    rw [show decide (n - countOnes v ≤ i.val) = false from by simp; omega]
    exact Bool.false_le _


/-! **ε-Halvers (Permutation-Based Definition)** -/

/-- Initial-segment halver property (AKS Section 3, permutation-based):
    for each initial segment `{0,...,k-1}` with `k ≤ n/2`, the number of
    positions from the bottom half (`rank pos ≥ n/2`) whose output element
    has rank < k is at most `ε · k`. -/
def EpsilonInitialHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  let n := Fintype.card α
  ∀ k : ℕ, k ≤ n / 2 →
    ((Finset.univ.filter (fun pos : α ↦
        n / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ) ≤ ε * k

/-- End-segment halver property: dual of `EpsilonInitialHalved` via order reversal. -/
def EpsilonFinalHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved (α := αᵒᵈ) w ε

/-- Val-based formulation of `EpsilonFinalHalved` on `Fin (2*m)`:
    positions in the first half `[0, m)` with large output values `≥ 2m - k`
    are bounded by `ε * k`. Bridges from `(Fin (2*m))ᵒᵈ` rank conditions
    to concrete `Fin (2*m)` val conditions. -/
lemma EpsilonFinalHalved.val_bound {m : ℕ} {w : Fin (2 * m) → Fin (2 * m)} {ε : ℝ}
    (h : EpsilonFinalHalved w ε) (k : ℕ) (hk : k ≤ m) :
    ((Finset.univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card : ℝ) ≤ ε * k := by
  unfold EpsilonFinalHalved EpsilonInitialHalved at h
  simp only [Fintype.card_orderDual, Fintype.card_fin,
    show 2 * m / 2 = m from by omega] at h
  have hbound := h k hk
  suffices hsuff : (Finset.univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card =
    (Finset.univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
      m ≤ @rank (Fin (2 * m))ᵒᵈ _ _ pos ∧
      @rank (Fin (2 * m))ᵒᵈ _ _ (w pos) < k)).card by
    exact_mod_cast hsuff ▸ hbound
  apply Finset.card_nbij'
    (fun x : Fin (2 * m) ↦ (OrderDual.toDual x : (Fin (2 * m))ᵒᵈ))
    (fun x : (Fin (2 * m))ᵒᵈ ↦ OrderDual.ofDual x)
  · intro x hx
    simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    constructor
    · show m ≤ @rank (Fin (2 * m))ᵒᵈ _ _ (OrderDual.toDual x)
      rw [rank_fin_od_val]; omega
    · show @rank (Fin (2 * m))ᵒᵈ _ _ (OrderDual.toDual (w x)) < k
      rw [rank_fin_od_val]
      have := (w x).isLt; omega
  · intro x hx
    simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hr1 : @rank (Fin (2 * m))ᵒᵈ _ _ x = 2 * m - 1 - (OrderDual.ofDual x).val :=
      rank_fin_od x
    have hr2 : @rank (Fin (2 * m))ᵒᵈ _ _ (w x) =
        2 * m - 1 - (w (OrderDual.ofDual x)).val := by
      show @rank (Fin (2 * m))ᵒᵈ _ _ (w x) = _
      exact rank_fin_od (w x)
    rw [hr1] at h1; rw [hr2] at h2
    have hx_lt := (OrderDual.ofDual x).isLt
    have hwx_lt := (w (OrderDual.ofDual x)).isLt
    constructor <;> omega
  · intro _ _; rfl
  · intro _ _; rfl

/-- A function is ε-halved if it satisfies both initial and final segment bounds. -/
def EpsilonHalved {α : Type*} [Fintype α] [LinearOrder α]
    (w : α → α) (ε : ℝ) : Prop :=
  EpsilonInitialHalved w ε ∧ EpsilonFinalHalved w ε

/-- A comparator network is an ε-halver if for every permutation input,
    the output is ε-halved.

    (AKS Section 3) This tracks labeled elements via permutations rather than
    0-1 values, which is essential for the segment-wise bounds — in the 0-1 case,
    same-valued elements are indistinguishable, making segment-wise counting
    impossible. -/
def IsEpsilonHalver {n : ℕ} (net : ComparatorNetwork n) (ε : ℝ) : Prop :=
  ∀ (v : Equiv.Perm (Fin n)),
    EpsilonHalved (net.exec v) ε

/-- `EpsilonInitialHalved` is monotone in ε: larger ε is weaker. -/
theorem EpsilonInitialHalved.mono {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε₁ ε₂ : ℝ} (h : EpsilonInitialHalved w ε₁) (hle : ε₁ ≤ ε₂) :
    EpsilonInitialHalved w ε₂ := by
  intro k hk
  calc ((Finset.univ.filter _).card : ℝ) ≤ ε₁ * k := h k hk
    _ ≤ ε₂ * k := by exact mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg k)

/-- `EpsilonHalved` is monotone in ε. -/
theorem EpsilonHalved.mono {α : Type*} [Fintype α] [LinearOrder α]
    {w : α → α} {ε₁ ε₂ : ℝ} (h : EpsilonHalved w ε₁) (hle : ε₁ ≤ ε₂) :
    EpsilonHalved w ε₂ :=
  ⟨h.1.mono hle, h.2.mono hle⟩

/-- `IsEpsilonHalver` is monotone in ε: a halver with error ε₁ is also
    a halver with any larger error ε₂ ≥ ε₁. -/
theorem IsEpsilonHalver.mono {n : ℕ} {net : ComparatorNetwork n}
    {ε₁ ε₂ : ℝ} (h : IsEpsilonHalver net ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonHalver net ε₂ :=
  fun v ↦ (h v).mono hle

/-- Merge two sorted halves using iterated ε-halvers.
    After k rounds of ε-halving, the "unsortedness" decreases
    geometrically: at most (2ε)^k · n elements are out of place. -/
def epsHalverMerge (n : ℕ) (k : ℕ)
    (halver : ComparatorNetwork n) : ComparatorNetwork n :=
  { comparators := (List.replicate k halver.comparators).flatten }


/-! **Top/Bottom Half Partitioning** -/

/-- Top half: positions with index < n/2 -/
def topHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ (i : ℕ) < n / 2)

/-- Bottom half: positions with index ≥ n/2 -/
def bottomHalf (n : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ n / 2 ≤ (i : ℕ))

/-- Top and bottom halves cover all positions -/
lemma topHalf_union_bottomHalf (n : ℕ) :
    topHalf n ∪ bottomHalf n = Finset.univ := by
  ext i
  simp [topHalf, bottomHalf]
  omega

/-- Top and bottom halves are disjoint -/
lemma topHalf_disjoint_bottomHalf (n : ℕ) :
    (topHalf n ∩ bottomHalf n) = ∅ := by
  ext i
  simp [topHalf, bottomHalf]

/-- Cardinality of top half -/
lemma card_topHalf (n : ℕ) : (topHalf n).card = n / 2 := by
  by_cases hn : n = 0
  · subst hn; simp [topHalf]
  · have hn2 : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) one_lt_two
    have : topHalf n = Finset.Iio ⟨n / 2, hn2⟩ := by
      ext ⟨i, hi⟩
      simp only [topHalf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio,
        Fin.lt_def]
    rw [this, Fin.card_Iio]

/-- Cardinality of bottom half -/
lemma card_bottomHalf (n : ℕ) : (bottomHalf n).card = n - n / 2 := by
  have h_union := topHalf_union_bottomHalf n
  have h_disj : Disjoint (topHalf n) (bottomHalf n) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (topHalf_disjoint_bottomHalf n)
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [h_union, Finset.card_univ, Fintype.card_fin, card_topHalf] at h_card
  omega

/-! **Halver Composition** -/

/-- An ε-sorted vector: at most εn elements are not in their
    correct sorted position. -/
def IsEpsilonSorted {n : ℕ} (v : Fin n → Bool) (ε : ℝ) : Prop :=
  ∃ (w : Fin n → Bool), Monotone w ∧
    ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n

/-! **Basic Properties of IsEpsilonSorted** -/

/-- Witness extraction helper -/
lemma IsEpsilonSorted.exists_witness {n : ℕ} {v : Fin n → Bool} {ε : ℝ}
    (h : IsEpsilonSorted v ε) :
    ∃ (w : Fin n → Bool), Monotone w ∧
      ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ) ≤ ε * n :=
  h

/-- Monotone Boolean sequences have the pattern 0* 1* (zeros then ones) -/
lemma Monotone.bool_pattern {n : ℕ} (w : Fin n → Bool) (hw : Monotone w) :
    ∃ k : ℕ, (∀ i : Fin n, (i : ℕ) < k → w i = false) ∧
             (∀ i : Fin n, k ≤ (i : ℕ) → w i = true) := by
  -- k = number of false values = size of the downward-closed false set
  use (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  set k := (Finset.univ.filter (fun i : Fin n ↦ w i = false)).card
  constructor
  · -- For i.val < k: w i = false
    intro ⟨i, hi⟩ h_lt
    by_contra h_not
    have h_true : w ⟨i, hi⟩ = true := by
      match h : w ⟨i, hi⟩ with
      | true => rfl
      | false => exact absurd h h_not
    -- Every j ≥ i has w j = true (by monotonicity)
    have h_above : ∀ j : Fin n, i ≤ j.val → w j = true := by
      intro ⟨j, hj⟩ h_ij
      have := hw (show (⟨i, hi⟩ : Fin n) ≤ ⟨j, hj⟩ from h_ij)
      rw [h_true] at this
      match h : w ⟨j, hj⟩ with
      | true => rfl
      | false => rw [h] at this; exact absurd this (by decide)
    -- So false set ⊆ {j | j.val < i}
    have h_sub : Finset.univ.filter (fun j : Fin n ↦ w j = false) ⊆
        Finset.Iio ⟨i, hi⟩ := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio, Fin.lt_def]
      by_contra h_ge; push_neg at h_ge
      exact absurd (h_above ⟨j, hj⟩ h_ge) (by simp [hm])
    -- Card of false set ≤ card of Iio = i
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iio] at this; omega
  · -- For k ≤ i.val: w i = true
    intro ⟨i, hi⟩ h_ge
    by_contra h_not
    have h_false : w ⟨i, hi⟩ = false := by
      match h : w ⟨i, hi⟩ with
      | false => rfl
      | true => exact absurd h h_not
    -- Every j ≤ i has w j = false (by monotonicity)
    have h_below : ∀ j : Fin n, j.val ≤ i → w j = false := by
      intro ⟨j, hj⟩ h_ji
      have := hw (show (⟨j, hj⟩ : Fin n) ≤ ⟨i, hi⟩ from h_ji)
      rw [h_false] at this
      match h : w ⟨j, hj⟩ with
      | false => rfl
      | true => rw [h] at this; exact absurd this (by decide)
    -- So Iic ⟨i, hi⟩ ⊆ false set
    have h_sub : Finset.Iic ⟨i, hi⟩ ⊆
        Finset.univ.filter (fun j : Fin n ↦ w j = false) := by
      intro ⟨j, hj⟩ hm
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h_below ⟨j, hj⟩ hm
    -- Card of Iic = i + 1 ≤ card of false set = k
    have := Finset.card_le_card h_sub
    rw [Fin.card_Iic] at this; omega

/-- Relaxation: if ε₁ ≤ ε₂, then ε₁-sorted implies ε₂-sorted -/
lemma IsEpsilonSorted.mono {n : ℕ} {v : Fin n → Bool} {ε₁ ε₂ : ℝ}
    (h : IsEpsilonSorted v ε₁) (hle : ε₁ ≤ ε₂) :
    IsEpsilonSorted v ε₂ := by
  obtain ⟨w, hw_mono, hw_card⟩ := h
  refine ⟨w, hw_mono, ?_⟩
  calc ((Finset.univ.filter (fun i ↦ v i ≠ w i)).card : ℝ)
      ≤ ε₁ * n := hw_card
    _ ≤ ε₂ * n := by apply mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)

/-- Every sequence is trivially 1-sorted -/
lemma isEpsilonSorted_one {n : ℕ} (v : Fin n → Bool) :
    IsEpsilonSorted v 1 := by
  -- Use the all-false sequence as witness
  refine ⟨fun _ ↦ false, ?_, ?_⟩
  · -- Constant false function is monotone
    intro a b _
    rfl
  · -- At most n positions can differ
    calc ((Finset.univ.filter (fun i ↦ v i ≠ false)).card : ℝ)
        ≤ Finset.univ.card := by
          exact_mod_cast Finset.card_mono (Finset.filter_subset _ _)
      _ = Fintype.card (Fin n) := by simp
      _ = n := by simp
      _ = 1 * n := by ring


/-! **Halver Family** -/

/-- A family of ε-halver networks at all even sizes, with bounded depth.
    The network `net m` operates on `2 * m` wires, covering sizes 0, 2, 4, 6, ...
    At `m = 0` the network operates on 0 wires (trivially halved by any network).

    The depth bound is fundamental: size ≤ m · depth follows from depth_le
    (each of depth rounds has ≤ m comparators on 2*m bipartite wires). -/
structure HalverFamily (ε : ℚ) where
  /-- Uniform depth bound for all networks in the family. -/
  depth : ℕ
  /-- The halver network for each index `m`. Operates on `2 * m` wires. -/
  net : (m : ℕ) → ComparatorNetwork (2 * m)
  /-- Each network is an ε-halver. -/
  isHalver : ∀ m, IsEpsilonHalver (net m) ↑ε
  /-- Each network has depth at most `depth`. -/
  depth_le : ∀ m, (net m).depth ≤ depth

/-- Depth ≤ depth on 2*m bipartite wires implies size ≤ m * depth. -/
theorem HalverFamily.size_le {ε : ℚ}
    (family : HalverFamily ε) (m : ℕ) :
    (family.net m).size ≤ m * family.depth := by
  have h1 := size_le_half_n_mul_depth (family.net m)
  have h2 := family.depth_le m
  have h3 : 2 * (family.net m).size ≤ 2 * (m * family.depth) :=
    calc 2 * (family.net m).size
        ≤ (2 * m) * (family.net m).depth := h1
      _ ≤ (2 * m) * family.depth := Nat.mul_le_mul_left _ h2
      _ = 2 * (m * family.depth) := by ring
  omega


/-! **Network Cast** -/

/-- Cast a comparator network to a different wire count via an equality proof. -/
def ComparatorNetwork.cast {n m : ℕ} (net : ComparatorNetwork n) (h : n = m) :
    ComparatorNetwork m :=
  h ▸ net

@[simp] lemma ComparatorNetwork.cast_depth {n m : ℕ}
    (net : ComparatorNetwork n) (h : n = m) :
    (net.cast h).depth = net.depth := by subst h; rfl

@[simp] lemma ComparatorNetwork.cast_isEpsilonHalver {n m : ℕ}
    (net : ComparatorNetwork n) (h : n = m) (ε : ℝ) :
    IsEpsilonHalver (net.cast h) ε ↔ IsEpsilonHalver net ε := by subst h; rfl

end


