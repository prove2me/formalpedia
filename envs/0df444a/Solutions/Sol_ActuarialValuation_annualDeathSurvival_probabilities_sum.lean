-- Prove2me | solution 1 for ActuarialValuation.annualDeathSurvival_probabilities_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:35:53.468783+00:00
-- url     : https://prove2.me/submissions/76812f98-4cff-4bca-8e43-d841551c15dd

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
import Theorems.Thm_ActuarialValuation_annualSurvivalMass_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K)
  (t : ℕ) (hS : 0 < annualSurvivalMass P K t)
  : annualDeathMass P K t / annualSurvivalMass P K t +
      annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t = 1 := by
  have hpart := annualSurvivalMass_partition P K hK t
  have hne : annualSurvivalMass P K t ≠ 0 := ne_of_gt hS
  calc
    annualDeathMass P K t / annualSurvivalMass P K t +
      annualSurvivalMass P K (t + 1) / annualSurvivalMass P K t =
        (annualDeathMass P K t + annualSurvivalMass P K (t + 1)) /
          annualSurvivalMass P K t := by rw [add_div]
    _ = annualSurvivalMass P K t / annualSurvivalMass P K t := by
      rw [← hpart]
    _ = 1 := div_self hne
