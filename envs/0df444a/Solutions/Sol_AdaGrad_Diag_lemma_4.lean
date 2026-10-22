-- Prove2me | solution 1 for AdaGrad.Diag.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:36:41.004088+00:00
-- url     : https://prove2.me/submissions/8f3f38af-4d2b-41f6-94bc-6c0165e93319

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup
import Theorems.Thm_AdaGrad_Diag_eq_24

open AdaGrad.Diag Finset

-- The scalar Auer–Gentile inequality is imported from vebis's accepted proof.
theorem solution {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, dualNormSq (s g t) (g t) ≤ 2 * ∑ i, s g T i := by
  classical
  unfold dualNormSq
  rw [sum_comm]
  calc
    _ ≤ ∑ i : Fin d, 2 * s g T i := by
      apply sum_le_sum
      intro i _
      exact eq_24 (fun t => g t i) T
    _ = _ := (mul_sum ..).symm
