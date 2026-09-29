-- Prove2me | solution 1 for AutomorphicForm.HeckeEigensystem.conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/acacd67c-6ae5-5304-8efd-6b5390bb2970

import Mathlib.Analysis.Complex.Norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq

set_option autoImplicit false

private theorem mul_conj_eq_of_norm_eq {b : ℂ} {c : ℝ} (h2 : ‖b‖ = c) :
    b * starRingEnd ℂ b = (c : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2, Complex.ofReal_pow]

private theorem conj_eq_div_of_mul_conj_eq_of_mul_conj_eq {a b c : ℂ}
    (h1 : a * starRingEnd ℂ b = c * starRingEnd ℂ a) (h2 : b * starRingEnd ℂ b = c ^ 2)
    (hc : c ≠ 0) :
    b ≠ 0 ∧ starRingEnd ℂ a = c * (a / b) ∧ starRingEnd ℂ b = c ^ 2 * b⁻¹ := by
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h2
    exact hc (by simpa using h2.symm)
  refine ⟨hb, ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff hb]
    apply mul_left_cancel₀ hc
    calc c * (starRingEnd ℂ a * b) = c * starRingEnd ℂ a * b := by ring
      _ = a * starRingEnd ℂ b * b := by rw [h1]
      _ = a * (b * starRingEnd ℂ b) := by ring
      _ = a * c ^ 2 := by rw [h2]
      _ = c * (c * a) := by ring
  · rw [← div_eq_mul_inv, eq_div_iff hb, mul_comm (starRingEnd ℂ b) b]
    exact h2

theorem solution
    (a b : ℂ) (c : ℝ) (hc : 0 < c)
    (h1 : a * starRingEnd ℂ b = (c : ℂ) * starRingEnd ℂ a) (h2 : ‖b‖ = c) :
    starRingEnd ℂ a = (c : ℂ) * (a / b) ∧ starRingEnd ℂ b = (c : ℂ) ^ 2 * b⁻¹ :=
  (conj_eq_div_of_mul_conj_eq_of_mul_conj_eq h1 (mul_conj_eq_of_norm_eq h2)
    (Complex.ofReal_ne_zero.mpr hc.ne')).2

end S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq
end P2MW
export P2MW.S_AutomorphicForm_HeckeEigensystem_conj_eq_mul_div_and_conj_eq_sq_mul_inv_of_mul_conj_eq_of_norm_eq (solution)
