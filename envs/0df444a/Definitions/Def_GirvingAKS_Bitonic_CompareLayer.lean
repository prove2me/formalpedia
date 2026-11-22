-- Prove2me | Definitions.Def_GirvingAKS_Bitonic_CompareLayer
-- name    : GirvingAKS_Bitonic_CompareLayer
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:40.476804+00:00
-- url     : https://prove2.me/theorems/9508c453-7ba8-4c06-a02c-82523cde1103
-- title:
--   AKS sorting networks (Seiferas port) — Bitonic Sort — Compare Layer Properties
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Bitonic/CompareLayer.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Left-le-right properties, compare layer preserves bitonic halves, merge sorts bitonic (main induction), exec_allFalse/True fixpoints.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Bitonic/CompareLayer.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Bitonic_LayerExec
import Definitions.Def_GirvingAKS_Bitonic_Bitonic01

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Bitonic/CompareLayer.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Bitonic Sort — Compare Layer Properties

  Left-le-right properties, compare layer preserves bitonic halves, merge sorts bitonic
  (main induction), exec_allFalse/True fixpoints.
-/


section

open Finset

/-! **Left le Right Property** -/

/-- After the compare layer on a bitonic input with `b=false`,
    either all AND values are false or all OR values are true. -/
theorem and_or_left_le_right_false {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (_hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = false ↔ lo ≤ j.val ∧ j.val < hi) :
    (∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = false) ∨
    (∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = true) := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases hcov : ∀ i : Fin m, (lo ≤ i.val ∧ i.val < hi) ∨ (lo ≤ i.val + m ∧ i.val + m < hi)
  · left; intro i; rw [Bool.and_eq_false_iff]
    rcases hcov i with h | h
    · exact Or.inl ((hvi i).mpr h)
    · exact Or.inr ((hvim i).mpr h)
  · right
    have ⟨i₀, hi₀⟩ := Classical.not_forall.mp hcov
    have hi₀1 : ¬(lo ≤ i₀.val ∧ i₀.val < hi) := fun h ↦ hi₀ (Or.inl h)
    have hi₀2 : ¬(lo ≤ i₀.val + m ∧ i₀.val + m < hi) := fun h ↦ hi₀ (Or.inr h)
    intro j
    cases hj1 : v ⟨j.val, by omega⟩ with
    | true => simp
    | false =>
      cases hj2 : v ⟨j.val + m, by omega⟩ with
      | true => simp
      | false =>
        exfalso
        have := (hvi j).mp hj1
        have := (hvim j).mp hj2
        omega

/-- After the compare layer on a bitonic input with `b=true`,
    either all AND values are false or all OR values are true. -/
theorem and_or_left_le_right_true {m : Nat} {v : Fin (2 * m) → Bool} {lo hi : Nat}
    (_hhi : hi ≤ 2 * m) (_hlo : lo ≤ hi)
    (hv : ∀ j : Fin (2 * m), v j = true ↔ lo ≤ j.val ∧ j.val < hi) :
    (∀ i : Fin m, (v ⟨i.val, by omega⟩ && v ⟨i.val + m, by omega⟩) = false) ∨
    (∀ i : Fin m, (v ⟨i.val, by omega⟩ || v ⟨i.val + m, by omega⟩) = true) := by
  have hvi := fun i ↦ isBitonic01_val_left hv i
  have hvim := fun i ↦ isBitonic01_val_right hv i
  by_cases hcov : ∀ i : Fin m, ¬((lo ≤ i.val ∧ i.val < hi) ∧ (lo ≤ i.val + m ∧ i.val + m < hi))
  · left; intro i; rw [Bool.and_eq_false_iff]
    have := hcov i
    by_cases h1 : v ⟨i.val, by omega⟩ = true
    · have h1i := (hvi i).mp h1
      have h2i : ¬(lo ≤ i.val + m ∧ i.val + m < hi) := fun hc ↦ this ⟨h1i, hc⟩
      right; cases hb : v ⟨i.val + m, by omega⟩ with
      | false => rfl
      | true => exact absurd ((hvim i).mp hb) h2i
    · left; cases hb : v ⟨i.val, by omega⟩ with
      | false => rfl
      | true => exact absurd hb h1
  · right
    have ⟨i₀, hi₀⟩ := Classical.not_forall.mp hcov
    have hi₀' : (lo ≤ i₀.val ∧ i₀.val < hi) ∧ (lo ≤ i₀.val + m ∧ i₀.val + m < hi) := by
      by_contra h; exact hi₀ h
    intro j
    cases hj1 : v ⟨j.val, by omega⟩ with
    | true => simp
    | false =>
      cases hj2 : v ⟨j.val + m, by omega⟩ with
      | true => simp
      | false =>
        exfalso
        have hni : ¬(lo ≤ j.val ∧ j.val < hi) := fun hc ↦ by
          have := (hvi j).mpr hc; rw [this] at hj1; exact Bool.noConfusion hj1
        have hnim : ¬(lo ≤ j.val + m ∧ j.val + m < hi) := fun hc ↦ by
          have := (hvim j).mpr hc; rw [this] at hj2; exact Bool.noConfusion hj2
        omega

/-! **Compare Layer Splits Bitonic into Bitonic Halves** -/

/-- After applying the compare layer to a bitonic input, the left half is bitonic. -/
theorem compare_layer_left_bitonic (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hv : IsBitonic01 v) :
    IsBitonic01 (fun i : Fin (2^k) ↦ (bitonicCompareLayer k).exec v
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  obtain ⟨b, lo, hi, hlo, hhi, hchar⟩ := hv
  have heq : ∀ i : Fin (2^k),
      (bitonicCompareLayer k).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
      (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
       v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) :=
    bitonicCompareLayer_exec_left k v
  suffices hsuff : IsBitonic01 (fun i : Fin (2^k) ↦
      v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ &&
      v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) by
    convert hsuff using 1; ext i; exact heq i
  have hhi2 : hi ≤ 2 * 2^k := by rw [Nat.pow_succ] at hhi; omega
  have hchar' : ∀ j : Fin (2 * 2^k), v ⟨j.val, by rw [Nat.pow_succ]; omega⟩ = b ↔
      lo ≤ j.val ∧ j.val < hi := by
    intro j; have := hchar ⟨j.val, by rw [Nat.pow_succ]; omega⟩; simpa using this
  cases b with
  | false =>
    obtain ⟨b', lo', hi', hlo', hhi', hchar''⟩ := and_bitonic_false hhi2 hlo hchar'
    exact ⟨b', lo', hi', hlo', hhi', fun i ↦ by
      have := hchar'' ⟨i.val, i.isLt⟩; simpa using this⟩
  | true =>
    obtain ⟨b', lo', hi', hlo', hhi', hchar''⟩ := and_bitonic_true hhi2 hlo hchar'
    exact ⟨b', lo', hi', hlo', hhi', fun i ↦ by
      have := hchar'' ⟨i.val, i.isLt⟩; simpa using this⟩

/-- After applying the compare layer to a bitonic input, the right half is bitonic. -/
theorem compare_layer_right_bitonic (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hv : IsBitonic01 v) :
    IsBitonic01 (fun i : Fin (2^k) ↦ (bitonicCompareLayer k).exec v
      ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) := by
  obtain ⟨b, lo, hi, hlo, hhi, hchar⟩ := hv
  have heq : ∀ i : Fin (2^k),
      (bitonicCompareLayer k).exec v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
      (v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ ||
       v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) :=
    bitonicCompareLayer_exec_right k v
  suffices hsuff : IsBitonic01 (fun i : Fin (2^k) ↦
      v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ ||
      v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩) by
    convert hsuff using 1; ext i; exact heq i
  have hhi2 : hi ≤ 2 * 2^k := by rw [Nat.pow_succ] at hhi; omega
  have hchar' : ∀ j : Fin (2 * 2^k), v ⟨j.val, by rw [Nat.pow_succ]; omega⟩ = b ↔
      lo ≤ j.val ∧ j.val < hi := by
    intro j; have := hchar ⟨j.val, by rw [Nat.pow_succ]; omega⟩; simpa using this
  cases b with
  | false =>
    obtain ⟨b', lo', hi', hlo', hhi', hchar''⟩ := or_bitonic_false hhi2 hlo hchar'
    exact ⟨b', lo', hi', hlo', hhi', fun i ↦ by
      have := hchar'' ⟨i.val, i.isLt⟩; simpa using this⟩
  | true =>
    obtain ⟨b', lo', hi', hlo', hhi', hchar''⟩ := or_bitonic_true hhi2 hlo hchar'
    exact ⟨b', lo', hi', hlo', hhi', fun i ↦ by
      have := hchar'' ⟨i.val, i.isLt⟩; simpa using this⟩

/-- After the compare layer on a bitonic input, left half le right half. -/
theorem compare_layer_left_le_right (k : Nat) (v : Fin (2^(k+1)) → Bool)
    (hv : IsBitonic01 v) :
    (∀ i : Fin (2^k), (bitonicCompareLayer k).exec v
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = false) ∨
    (∀ i : Fin (2^k), (bitonicCompareLayer k).exec v
      ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ = true) := by
  obtain ⟨b, lo, hi, hlo, hhi, hchar⟩ := hv
  have hhi2 : hi ≤ 2 * 2^k := by rw [Nat.pow_succ] at hhi; omega
  have hchar' : ∀ j : Fin (2 * 2^k), v ⟨j.val, by rw [Nat.pow_succ]; omega⟩ = b ↔
      lo ≤ j.val ∧ j.val < hi := by
    intro j; have := hchar ⟨j.val, by rw [Nat.pow_succ]; omega⟩; simpa using this
  have hlr := by
    cases b with
    | false => exact and_or_left_le_right_false hhi2 hlo hchar'
    | true => exact and_or_left_le_right_true hhi2 hlo hchar'
  rcases hlr with h | h
  · left; intro i
    rw [bitonicCompareLayer_exec_left]
    exact h ⟨i.val, i.isLt⟩
  · right; intro i
    rw [bitonicCompareLayer_exec_right]
    exact h ⟨i.val, i.isLt⟩

/-! **Bitonic Merge Sorts Bitonic** -/

/-- If a comparator network maps all-false to all-false, then all-false is a fixpoint. -/
theorem exec_allFalse_eq {n : Nat} (net : ComparatorNetwork n) :
    net.exec (fun _ : Fin n ↦ false) = (fun _ ↦ false) := by
  ext i; unfold ComparatorNetwork.exec
  induction net.comparators generalizing i with
  | nil => simp [List.foldl]
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have : c.apply (fun _ ↦ false) = (fun _ ↦ false) := by
      ext k; unfold Comparator.apply
      split_ifs <;> simp
    rw [this]; exact ih i

/-- If a comparator network maps all-true to all-true, then all-true is a fixpoint. -/
theorem exec_allTrue_eq {n : Nat} (net : ComparatorNetwork n) :
    net.exec (fun _ : Fin n ↦ true) = (fun _ ↦ true) := by
  ext i; unfold ComparatorNetwork.exec
  induction net.comparators generalizing i with
  | nil => simp [List.foldl]
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have : c.apply (fun _ ↦ true) = (fun _ ↦ true) := by
      ext k; unfold Comparator.apply
      split_ifs <;> simp
    rw [this]; exact ih i

/-- Helper: characterize the result of the merge network at positions in the left half. -/
theorem merge_result_left (k : Nat) (w : Fin (2^(k+1)) → Bool)
    (h0 : 0 + 2^k ≤ 2^(k+1)) (h1 : 2^k + 2^k ≤ 2^(k+1))
    (wL : Fin (2^k) → Bool)
    (hwL : wL = fun i ↦ w ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩)
    (i : Fin (2^k)) :
    ((bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1).exec
      (((bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0).exec w)
      ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
    (bitonicMerge k).exec wL i := by
  have hout := ComparatorNetwork.shiftEmbed_exec_outside
    (bitonicMerge k) (2^(k+1)) (2^k) h1
    (((bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0).exec w)
    ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    (Or.inl (by show i.val < 2^k; exact i.isLt))
  rw [hout]
  rw [shiftEmbed_zero_exec]
  congr 1; rw [hwL]

/-- Helper: characterize the result of the merge network at positions in the right half. -/
theorem merge_result_right (k : Nat) (w : Fin (2^(k+1)) → Bool)
    (h0 : 0 + 2^k ≤ 2^(k+1)) (h1 : 2^k + 2^k ≤ 2^(k+1))
    (wR : Fin (2^k) → Bool)
    (hwR : wR = fun i ↦ w ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩)
    (i : Fin (2^k)) :
    ((bitonicMerge k).shiftEmbed (2^(k+1)) (2^k) h1).exec
      (((bitonicMerge k).shiftEmbed (2^(k+1)) 0 h0).exec w)
      ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
    (bitonicMerge k).exec wR i := by
  rw [shiftEmbed_offset_exec]
  congr 1; ext j
  have hout := ComparatorNetwork.shiftEmbed_exec_outside
    (bitonicMerge k) (2^(k+1)) 0 h0 w
    ⟨j.val + 2^k, by have := j.isLt; rw [Nat.pow_succ]; omega⟩
    (Or.inr (by show 0 + 2^k ≤ j.val + 2^k; omega))
  rw [hout, hwR]

/-- Bitonic merge sorts bitonic 0-1 inputs: the output is monotone. -/
theorem bitonicMerge_sorts_bitonic_bool :
    ∀ (k : Nat) (v : Fin (2^k) → Bool), IsBitonic01 v → Monotone ((bitonicMerge k).exec v) := by
  intro k
  induction k with
  | zero =>
    intro v _ a b _
    have ha : a = ⟨0, by omega⟩ := Fin.ext (by omega)
    have hb : b = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [ha, hb]
  | succ k ih =>
    intro v hv
    have h0 : 0 + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    have h1 : 2^k + 2^k ≤ 2^(k+1) := by rw [Nat.pow_succ]; omega
    -- Decompose execution
    have hdecomp := bitonicMerge_exec_eq k v
    -- After compare layer
    set w := (bitonicCompareLayer k).exec v with hw_def
    -- After compare layer, left half is bitonic, right half is bitonic, left le right
    have hleft_bito := compare_layer_left_bitonic k v hv
    have hright_bito := compare_layer_right_bitonic k v hv
    have hlr := compare_layer_left_le_right k v hv
    -- Define the local views
    set wL : Fin (2^k) → Bool := fun i ↦ w ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    set wR : Fin (2^k) → Bool := fun i ↦ w ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩
    -- By IH, merge sorts each half
    have hml : Monotone ((bitonicMerge k).exec wL) := ih wL hleft_bito
    have hmr : Monotone ((bitonicMerge k).exec wR) := ih wR hright_bito
    -- Characterize the full output at each position
    have hw2_left : ∀ i : Fin (2^k),
        (bitonicMerge (k + 1)).exec v ⟨i.val, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
        (bitonicMerge k).exec wL i := by
      intro i; rw [hdecomp]; exact merge_result_left k w h0 h1 wL rfl i
    have hw2_right : ∀ i : Fin (2^k),
        (bitonicMerge (k + 1)).exec v ⟨i.val + 2^k, by have := i.isLt; rw [Nat.pow_succ]; omega⟩ =
        (bitonicMerge k).exec wR i := by
      intro i; rw [hdecomp]; exact merge_result_right k w h0 h1 wR rfl i
    -- Prove monotonicity by case analysis
    intro a b hab
    by_cases ha : a.val < 2^k
    · by_cases hb : b.val < 2^k
      · -- Both in left half
        have ha' : (a : Fin (2^(k+1))) = ⟨a.val, a.isLt⟩ := rfl
        have hb' : (b : Fin (2^(k+1))) = ⟨b.val, b.isLt⟩ := rfl
        rw [ha', hb', hw2_left ⟨a.val, ha⟩, hw2_left ⟨b.val, hb⟩]
        exact hml (Fin.mk_le_mk.mpr hab)
      · -- a in left, b in right
        have hb_eq : (b : Fin (2^(k+1))) = ⟨(b.val - 2^k) + 2^k, by omega⟩ :=
          Fin.ext (by show b.val = (b.val - 2^k) + 2^k; omega)
        have ha' : (a : Fin (2^(k+1))) = ⟨a.val, a.isLt⟩ := rfl
        rw [ha', hw2_left ⟨a.val, ha⟩, hb_eq, hw2_right ⟨b.val - 2^k, by omega⟩]
        rcases hlr with hlr | hlr
        · have : wL = fun _ ↦ false := by ext i; exact hlr i
          rw [this, exec_allFalse_eq]; exact Bool.false_le _
        · have : wR = fun _ ↦ true := by ext i; exact hlr i
          rw [this, exec_allTrue_eq]; exact Bool.le_true _
    · -- a in right half (and so is b since a le b)
      have ha_eq : (bitonicMerge (k+1)).exec v a =
          (bitonicMerge k).exec wR ⟨a.val - 2^k, by omega⟩ := by
        conv_lhs => rw [show (a : Fin (2^(k+1))) = ⟨(a.val - 2^k) + 2^k, by omega⟩ from
          Fin.ext (by show a.val = (a.val - 2^k) + 2^k; omega)]
        exact hw2_right ⟨a.val - 2^k, by omega⟩
      have hb_eq : (bitonicMerge (k+1)).exec v b =
          (bitonicMerge k).exec wR ⟨b.val - 2^k, by omega⟩ := by
        conv_lhs => rw [show (b : Fin (2^(k+1))) = ⟨(b.val - 2^k) + 2^k, by omega⟩ from
          Fin.ext (by show b.val = (b.val - 2^k) + 2^k; omega)]
        exact hw2_right ⟨b.val - 2^k, by omega⟩
      rw [ha_eq, hb_eq]
      exact hmr (Fin.mk_le_mk.mpr (by omega))

end


