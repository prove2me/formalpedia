-- Prove2me | solution 1 for AkhmedovNeutrino.matter_amplitude_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T10:13:19.00087+00:00
-- url     : https://prove2.me/submissions/068cd8ef-3fdb-471e-8ad2-e4b92cc83b1b

import Mathlib
import Definitions.Def_AkhmedovNeutrino_MSW

set_option autoImplicit false

open AkhmedovNeutrino in
theorem solution (Δm2 E θ0 GF Ne θ : ℝ) (hE : 0 < E)
    (hgap : matterEnergyGap Δm2 E θ0 GF Ne ≠ 0)
    (hcos : matterEnergyGap Δm2 E θ0 GF Ne * Real.cos (2 * θ) =
      Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne)
    (hsin : matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ) =
      Δm2 / (2 * E) * Real.sin (2 * θ0)) :
    Real.sin (2 * θ) ^ 2 = matterOscAmplitude Δm2 E θ0 GF Ne := by
  have hD : 0 ≤ (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
      + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 := by positivity
  have hsq : matterEnergyGap Δm2 E θ0 GF Ne ^ 2 =
      (Δm2 / (2 * E) * Real.cos (2 * θ0) - ccPotential GF Ne) ^ 2
      + (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 := by
    unfold matterEnergyGap
    exact Real.sq_sqrt hD
  have hg2 : matterEnergyGap Δm2 E θ0 GF Ne ^ 2 ≠ 0 := pow_ne_zero 2 hgap
  have hnum : (Δm2 / (2 * E)) ^ 2 * Real.sin (2 * θ0) ^ 2 =
      (matterEnergyGap Δm2 E θ0 GF Ne * Real.sin (2 * θ)) ^ 2 := by
    rw [hsin]
    ring
  unfold matterOscAmplitude
  rw [← hsq, hnum, eq_div_iff hg2]
  ring
