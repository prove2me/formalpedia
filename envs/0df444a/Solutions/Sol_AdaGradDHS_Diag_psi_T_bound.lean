-- Prove2me | solution 1 for AdaGradDHS.Diag.psi_T_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:37:59.34918+00:00
-- url     : https://prove2.me/submissions/b69e7d7b-1607-4ed3-b05b-0b2df450ff0a

import Mathlib
import Definitions.Def_AdaGradDHS_Diag_accNorm
import Definitions.Def_AdaGradDHS_Diag_adagradPsi
import Definitions.Def_AdaGradDHS_Diag_supNorm

open AdaGradDHS.Diag in
theorem solution {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) :
    2 * adagradPsi δ g T xstar = δ * ‖xstar‖ ^ 2 + ∑ i, accNorm g T i * (xstar i) ^ 2 ∧
      δ * ‖xstar‖ ^ 2 + ∑ i, accNorm g T i * (xstar i) ^ 2 ≤
        δ * ‖xstar‖ ^ 2 + supNorm xstar ^ 2 * ∑ i, accNorm g T i := by
  have hn : ‖xstar‖ ^ 2 = ∑ i, xstar i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  refine ⟨?_, ?_⟩
  · unfold adagradPsi
    rw [hn]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · have hsq : ∀ i, xstar i ^ 2 ≤ supNorm xstar ^ 2 := by
      intro i
      have h1 : (‖xstar i‖₊ : ℝ) ≤ supNorm xstar :=
        NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => ‖xstar i‖₊) (Finset.mem_univ i))
      rw [coe_nnnorm, Real.norm_eq_abs] at h1
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hacc : ∀ i, 0 ≤ accNorm g T i := fun i => Real.sqrt_nonneg _
    have : ∑ i, accNorm g T i * xstar i ^ 2 ≤ supNorm xstar ^ 2 * ∑ i, accNorm g T i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => by
        rw [mul_comm (supNorm xstar ^ 2)]
        exact mul_le_mul_of_nonneg_left (hsq i) (hacc i))
    linarith
