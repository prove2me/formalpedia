-- Prove2me | solution 1 for ActuarialValuation.csCauseInsurancePV_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:03.123772+00:00
-- url     : https://prove2.me/submissions/160d32a7-f59a-483c-a326-8a31dae4feb6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseInsurancePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ) (disc : ℝ) :
    csCauseInsurancePV μ U V Z disc 0 0 0 = 0 := by
  simp [csCauseInsurancePV]
