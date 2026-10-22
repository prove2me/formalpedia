-- Prove2me | solution 1 for AdaGrad.Diag.primal_dual_gradient_term
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:39:36.345892+00:00
-- url     : https://prove2.me/submissions/97cfe3d9-daed-46f2-be6c-0abfc13bb821

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup
import Theorems.Thm_AdaGrad_Diag_lemma_4

open AdaGrad.Diag Finset

private lemma current_zero {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (ht : 1 ≤ t) (i : Fin d) (hz : s g t i = 0) : g t i = 0 := by
  have hs : (s g t i)^2 = ∑ r ∈ Icc 1 t, (g r i)^2 :=
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hle : (g t i)^2 ≤ ∑ r ∈ Icc 1 t, (g r i)^2 :=
    single_le_sum (fun r _ => sq_nonneg (g r i)) (mem_Icc.mpr ⟨ht, le_rfl⟩)
  rw [hz] at hs
  nlinarith [sq_nonneg (g t i)]

private lemma s_succ_square {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d))
    (t : ℕ) (i : Fin d) :
    (s g (t+1) i)^2 = (s g t i)^2 + (g (t+1) i)^2 := by
  have hs (n : ℕ) : (s g n i)^2 = ∑ r ∈ Icc 1 n, (g r i)^2 :=
    Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  rw [hs, hs, sum_Icc_succ_top (by omega)]

theorem solution {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hδ : 0 ≤ δ) (T : ℕ) (hδg : ∀ t ∈ Finset.Icc 1 T, supNorm (g t) ≤ δ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (adaWeights δ g (t - 1)) (g t) ≤ 2 * ∑ i, s g T i := by
  classical
  calc
    _ ≤ ∑ t ∈ Icc 1 T, dualNormSq (s g t) (g t) := by
      apply sum_le_sum
      intro t ht
      apply sum_le_sum
      intro i _
      have ht1 : 1 ≤ t := (mem_Icc.mp ht).1
      have hi : |g t i| ≤ δ := by
        apply le_trans _ (hδg t ht)
        exact le_ciSup (Finite.bddAbove_range (fun j : Fin d => |g t j|)) i
      have hs := s_succ_square g (t-1) i
      rw [Nat.sub_add_cancel ht1] at hs
      have hprev : 0 ≤ s g (t-1) i := Real.sqrt_nonneg _
      have hcurr : 0 ≤ s g t i := Real.sqrt_nonneg _
      have ha : 0 ≤ |g t i| := abs_nonneg _
      have hweight : s g t i ≤ adaWeights δ g (t-1) i := by
        unfold adaWeights
        have htriangle : s g t i ≤ s g (t-1) i + |g t i| := by
          nlinarith [sq_abs (g t i), mul_nonneg hprev ha]
        linarith
      by_cases hz : s g t i = 0
      · have hg := current_zero g t ht1 i hz
        simp [hg]
      · exact div_le_div_of_nonneg_left (sq_nonneg _)
          (lt_of_le_of_ne hcurr (Ne.symm hz)) hweight
    _ ≤ _ := lemma_4 g T
