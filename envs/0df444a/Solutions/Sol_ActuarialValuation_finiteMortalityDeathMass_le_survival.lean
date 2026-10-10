-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityDeathMass_le_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:07.678851+00:00
-- url     : https://prove2.me/submissions/c544e026-d79f-45f9-a8ab-01b884d126e8

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hw : ∀ ω, 0 ≤ w ω)
  :
  finiteMortalityDeathMass w K t ≤ finiteMortalitySurvivalMass w K t := by
  unfold finiteMortalityDeathMass finiteMortalitySurvivalMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : K ω = t
  · have ht : t ≤ K ω := by omega
    simp [h, ht]
  · by_cases ht : t ≤ K ω
    · simp [h, ht, hw ω]
    · simp [h, ht]
