-- Prove2me | solution 1 for AkhmedovNeutrino.msw_resonance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T10:13:19.005775+00:00
-- url     : https://prove2.me/submissions/027470a4-a182-455d-9a0f-7ef0efa3990d

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF Ne : ℝ) (hE : 0 < E) :
    matterOscAmplitude Δm2 E θ0 GF Ne ≤ 1 ∧
    (Δm2 / (2 * E) * Real.sin (2 * θ0) ≠ 0 →
      (matterOscAmplitude Δm2 E θ0 GF Ne = 1 ↔
        ccPotential GF Ne = Δm2 / (2 * E) * Real.cos (2 * θ0))) := by
  have hY : (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 =
      (Δm2 / (2 * E) * Real.sin (2 * θ0)) ^ 2 := by ring
  unfold matterOscAmplitude
  rw [hY]
  refine ⟨?_, ?_⟩
  · apply div_le_one_of_le₀
    · nlinarith [sq_nonneg (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)]
    · positivity
  · intro hne
    have hYpos : 0 < (Δm2 / (2 * E) * Real.sin (2 * θ0)) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hne).symm
    have hDpos : 0 < (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2 +
        (Δm2 / (2 * E) * Real.sin (2 * θ0)) ^ 2 := by positivity
    rw [div_eq_one_iff_eq hDpos.ne']
    constructor
    · intro h
      have hX0 : (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2 = 0 := by
        linarith
      have hX : Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne = 0 :=
        pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hX0
      linarith
    · intro h
      rw [h]
      ring
