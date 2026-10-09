-- Prove2me | solution 2 for ActuarialValuation.annualSurvivalMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:18:47.839432+00:00
-- url     : https://prove2.me/submissions/c75609f7-7526-480f-a40a-4e7f9463e90c

import Mathlib
import Definitions.Def_actuarial_annualSurvivalMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K) :
    annualSurvivalMass P K 0 = 1 := by
  have hset : {ω : Ω | (0 : ℕ) ≤ K ω} = Set.univ := by
    ext ω
    simp
  simp [annualSurvivalMass, hset]
