-- Prove2me | solution 1 for AdaGrad.Diag.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:39:30.570152+00:00
-- url     : https://prove2.me/submissions/8f5524ed-b4f0-48ab-9984-f8da316c9055

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

theorem solution {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hδ : 0 ≤ δ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (adaWeights δ g t) (g t) ≤ 2 * ∑ i, s g T i := by
  classical
  calc
    _ ≤ ∑ t ∈ Icc 1 T, dualNormSq (s g t) (g t) := by
      apply sum_le_sum
      intro t ht
      apply sum_le_sum
      intro i _
      by_cases hz : s g t i = 0
      · have hg := current_zero g t (mem_Icc.mp ht).1 i hz
        simp [hg]
      · have hp : 0 < s g t i := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
        exact div_le_div_of_nonneg_left (sq_nonneg _) hp (by
          unfold adaWeights
          linarith)
    _ ≤ _ := lemma_4 g T
