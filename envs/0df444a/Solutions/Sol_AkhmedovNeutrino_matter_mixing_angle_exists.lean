-- Prove2me | solution 1 for AkhmedovNeutrino.matter_mixing_angle_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T10:37:48.279239+00:00
-- url     : https://prove2.me/submissions/91797e06-d2a1-4450-b55b-d1cb6c36f644

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false
set_option linter.unusedVariables false

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E) :
    ∃ θ : ℝ,
      matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
          Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne ∧
      matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
          Δm2 / (2 * E) * Real.sin (2 * θ0) ∧
      (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne ≠ 0 →
        Real.tan (2 * θ) = Δm2 / (2 * E) * Real.sin (2 * θ0) /
          (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)) := by
  set z : ℂ := ⟨Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne,
    Δm2 / (2 * E) * Real.sin (2 * θ0)⟩ with hz
  have hg : matterEnergyGap Δm2 E θ0 GF Ne = ‖z‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    unfold matterEnergyGap
    congr 1
    show _ = (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2 +
      (Δm2 / (2 * E) * Real.sin (2 * θ0)) ^ 2
    ring
  have h1 : matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * (Complex.arg z / 2)) =
      Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne := by
    rw [show 2 * (Complex.arg z / 2) = Complex.arg z by ring, hg]
    exact Complex.norm_mul_cos_arg z
  have h2 : matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * (Complex.arg z / 2)) =
      Δm2 / (2 * E) * Real.sin (2 * θ0) := by
    rw [show 2 * (Complex.arg z / 2) = Complex.arg z by ring, hg]
    exact Complex.norm_mul_sin_arg z
  refine ⟨Complex.arg z / 2, h1, h2, ?_⟩
  intro hX
  have hc : Real.cos (2 * (Complex.arg z / 2)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h1
    exact hX h1.symm
  rw [Real.tan_eq_sin_div_cos, div_eq_div_iff hc hX]
  linear_combination Real.cos (2 * (Complex.arg z / 2)) * h2 -
    Real.sin (2 * (Complex.arg z / 2)) * h1
