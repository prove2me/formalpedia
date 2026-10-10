-- Prove2me | solution 1 for ActuarialValuation.finiteMortalityRates_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:54:59.784863+00:00
-- url     : https://prove2.me/submissions/52a9b99b-a15c-43e7-acb8-f336cd767c71

import Mathlib
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (K : Ω → ℕ) (t : ℕ) (hS : 0 < finiteMortalitySurvivalMass w K t)
  :
  finiteMortalityDeathRate w K t + finiteMortalitySurvivalRate w K t = 1 := by
  have hp : finiteMortalitySurvivalMass w K t =
      finiteMortalityDeathMass w K t + finiteMortalitySurvivalMass w K (t + 1) := by
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
  change finiteMortalityDeathMass w K t / finiteMortalitySurvivalMass w K t +
    finiteMortalitySurvivalMass w K (t + 1) / finiteMortalitySurvivalMass w K t = 1
  rw [← add_div, ← hp]
  exact div_self (ne_of_gt hS)
