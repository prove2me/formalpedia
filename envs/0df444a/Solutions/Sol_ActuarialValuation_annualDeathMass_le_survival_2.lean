-- Prove2me | solution 2 for ActuarialValuation.annualDeathMass_le_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:55.089883+00:00
-- url     : https://prove2.me/submissions/ed0baafb-eb96-456a-b03c-3b16d9b1e95d

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) (t : ℕ) :
    annualDeathMass P K t ≤ annualSurvivalMass P K t := by
  unfold annualDeathMass annualSurvivalMass
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  omega
