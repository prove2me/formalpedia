-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityMass_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:52:00.736035+00:00
-- url     : https://prove2.me/submissions/b0dd3d7f-dea8-4757-8e94-6aae92e73ea8

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ)
  :
  finiteMortalitySurvivalMass w K t = finiteMortalityDeathMass w K t + finiteMortalitySurvivalMass w K (t + 1) := by
  unfold finiteMortalitySurvivalMass finiteMortalityDeathMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : K ω = t
  · have ht : t ≤ K ω := by omega
    have ht1 : ¬ t + 1 ≤ K ω := by omega
    simp [h, ht, ht1]
  · by_cases ht : t ≤ K ω
    · have ht1 : t + 1 ≤ K ω := by omega
      simp [h, ht, ht1]
    · have ht1 : ¬ t + 1 ≤ K ω := by omega
      simp [h, ht, ht1]
