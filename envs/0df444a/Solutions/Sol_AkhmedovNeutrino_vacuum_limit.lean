-- Prove2me | solution 1 for AkhmedovNeutrino.vacuum_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:37:57.052539+00:00
-- url     : https://prove2.me/submissions/840ca7ec-362f-4042-9e7f-563e53267c29

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF : ℝ) (hE : 0 < E) (hΔ : Δm2 ≠ 0) :
    matterOscAmplitude Δm2 E θ0 GF 0 = Real.sin (2 * θ0) ^ 2 ∧
    matterOscLength Δm2 E θ0 GF 0 = |vacuumOscLength Δm2 E| := by
  have hc : ccPotential GF 0 = 0 := by simp [ccPotential]
  have ha : Δm2 / (2 * E) ≠ 0 := div_ne_zero hΔ (by positivity)
  have hden : (Δm2 / (2 * E) * Real.cos (2 * θ0) - 0) ^ 2
      + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 = (Δm2 / (2 * E)) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (2 * θ0)
    linear_combination (Δm2 / (2 * E)) ^ 2 * h
  constructor
  · unfold matterOscAmplitude
    rw [hc, hden]
    field_simp
  · unfold matterOscLength matterEnergyGap vacuumOscLength
    rw [hc, hden, Real.sqrt_sq_eq_abs, abs_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * E),
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi * E)]
    have hΔ' : |Δm2| ≠ 0 := abs_ne_zero.mpr hΔ
    field_simp
    ring
#print axioms solution
