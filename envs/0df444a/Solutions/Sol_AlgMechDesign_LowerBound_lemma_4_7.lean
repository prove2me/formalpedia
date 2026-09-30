-- Prove2me | solution 1 for AlgMechDesign.LowerBound.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:18:24.979569+00:00
-- url     : https://prove2.me/submissions/fa68b748-6861-4cb5-ab0a-ce5cc3176f0f

import Theorems.Thm_AlgMechDesign_LowerBound_maximization

set_option autoImplicit false
open AlgMechDesign.LowerBound Finset

private theorem time_sdiff {k : ℕ} (ti : Fin k → ℝ) {A B : Finset (Fin k)} (h : A ⊆ B) :
    taskTime ti (B \ A) = taskTime ti B - taskTime ti A := by
  exact Finset.sum_sdiff_eq_sub h

private theorem diff_of_subset {n k : ℕ}
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (i : Fin n) (t : Fin n → Fin k → ℝ)
    {A B : Finset (Fin k)} (h : A ⊆ B) :
    priceDiff alloc pay i t A (B \ A) = price alloc pay i B t - price alloc pay i A t := by
  simp only [priceDiff, Finset.union_sdiff_of_subset h]

theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (X : Finset (Fin k)) (hX : X = taskSet (alloc t) i) :
    (∀ D : Finset (Fin k), IsAttainable alloc i t D → D ≠ X →
      (D ⊂ X → taskTime (t i) (X \ D) ≤ priceDiff alloc pay i t D (X \ D)) ∧
      (X ⊂ D → priceDiff alloc pay i t X (D \ X) ≤ taskTime (t i) (D \ X)) ∧
      (¬ D ⊆ X → ¬ X ⊆ D →
        priceDiff alloc pay i t (D ∩ X) (D \ (D ∩ X)) - taskTime (t i) (D \ (D ∩ X)) ≤
          priceDiff alloc pay i t (D ∩ X) (X \ (D ∩ X)) - taskTime (t i) (X \ (D ∩ X)))) ∧
    (∀ Y : Finset (Fin k), IsAttainable alloc i t Y →
      (∀ D : Finset (Fin k), IsAttainable alloc i t D → D ≠ Y →
        (D ⊂ Y → taskTime (t i) (Y \ D) < priceDiff alloc pay i t D (Y \ D)) ∧
        (Y ⊂ D → priceDiff alloc pay i t Y (D \ Y) < taskTime (t i) (D \ Y)) ∧
        (¬ D ⊆ Y → ¬ Y ⊆ D →
          priceDiff alloc pay i t (D ∩ Y) (D \ (D ∩ Y)) - taskTime (t i) (D \ (D ∩ Y)) <
            priceDiff alloc pay i t (D ∩ Y) (Y \ (D ∩ Y)) - taskTime (t i) (Y \ (D ∩ Y)))) →
      Y = X) := by
  have hmax := maximization alloc pay htruth t ht i
  rw [← hX] at hmax
  constructor
  · intro D hD hne
    have hm := hmax.2 D hD
    refine ⟨?_, ?_, ?_⟩
    · intro hsub
      rw [time_sdiff (t i) hsub.subset, diff_of_subset alloc pay i t hsub.subset]
      linarith
    · intro hsub
      rw [time_sdiff (t i) hsub.subset, diff_of_subset alloc pay i t hsub.subset]
      linarith
    · intro hd hx
      rw [time_sdiff (t i) Finset.inter_subset_left,
        time_sdiff (t i) Finset.inter_subset_right,
        diff_of_subset alloc pay i t Finset.inter_subset_left,
        diff_of_subset alloc pay i t Finset.inter_subset_right]
      linarith
  · intro Y hY hstrict
    by_contra hne
    have hm := hmax.2 Y hY
    have hs := hstrict X hmax.1 (Ne.symm hne)
    by_cases hXY : X ⊆ Y
    · have hproper : X ⊂ Y := Finset.ssubset_iff_subset_ne.mpr ⟨hXY, Ne.symm hne⟩
      have hh := hs.1 hproper
      rw [time_sdiff (t i) hXY, diff_of_subset alloc pay i t hXY] at hh
      linarith
    · by_cases hYX : Y ⊆ X
      · have hproper : Y ⊂ X := Finset.ssubset_iff_subset_ne.mpr ⟨hYX, hne⟩
        have hh := hs.2.1 hproper
        rw [time_sdiff (t i) hYX, diff_of_subset alloc pay i t hYX] at hh
        linarith
      · have hh := hs.2.2 hXY hYX
        rw [time_sdiff (t i) Finset.inter_subset_left,
          time_sdiff (t i) Finset.inter_subset_right,
          diff_of_subset alloc pay i t Finset.inter_subset_left,
          diff_of_subset alloc pay i t Finset.inter_subset_right] at hh
        linarith
