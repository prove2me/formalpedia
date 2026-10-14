-- Prove2me | solution 1 for ActuarialValuation.csCauseInsurancePV_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:00:46.046894+00:00
-- url     : https://prove2.me/submissions/fdbd7278-bd99-498d-903e-1e59fe2c5ec1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_csCauseInsurancePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    (disc b1 b2 bz k : ℝ) :
    csCauseInsurancePV μ U V Z disc (k*b1) (k*b2) (k*bz) =
      k * csCauseInsurancePV μ U V Z disc b1 b2 bz := by
  unfold csCauseInsurancePV
  ring
