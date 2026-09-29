-- Prove2me | solution 1 for AKR2008.singlet_reduced_trace_00_eval
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:07:32.303986+00:00
-- url     : https://prove2.me/submissions/23cfc40f-8b4b-4e37-962e-4f6607f33068

import Definitions.Def_AKR2008_Defs

open AKR2008
open scoped InnerProductSpace

theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Φ₀ : H) (h₀ : ‖Φ₀‖ = 1) :
    reducedPhoton2 (psiBefore Φ₀) 0 0 = 1 / 2 := by
  have hinner : ⟪Φ₀, Φ₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, h₀]
    norm_num
  have hroot : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp [reducedPhoton2, psiBefore, polKet, Fin.sum_univ_two,
    inner_smul_left, inner_smul_right, hinner, hroot]
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [norm_smul, h₀, mul_one, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hsqrtpos]
  norm_cast
  rw [inv_pow, hroot]
  norm_num
