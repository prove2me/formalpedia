-- Prove2me | solution 1 for ActuarialValuation.annualDeathMass_le_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:16.49438+00:00
-- url     : https://prove2.me/submissions/f28219f1-4358-4250-8a28-bfbdbad418d2

import Mathlib
import Definitions.Def_actuarial_annualDeathMass
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (K : Ω → ℕ) (hK : Measurable K) (t : ℕ)
  : annualDeathMass P K t ≤ annualSurvivalMass P K t := by
  unfold annualDeathMass annualSurvivalMass
  apply ENNReal.toReal_mono (measure_ne_top P _)
  apply measure_mono
  intro ω hω
  change K ω = t at hω
  change t ≤ K ω
  omega
