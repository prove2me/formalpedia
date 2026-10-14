-- Prove2me | solution 1 for ActuarialValuation.csBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:19:17.221695+00:00
-- url     : https://prove2.me/submissions/3c6d5aef-15c3-48f7-ba0f-ecb16af0a7dd

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
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (disc b1 b2 bz : ℝ) (hd : 0 ≤ disc)
    (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (hz : 0 ≤ bz) :
    0 ≤ csCauseInsurancePV μ U V Z disc b1 b2 bz := by
  unfold csCauseInsurancePV
  apply mul_nonneg hd
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg h1 ENNReal.toReal_nonneg
    · exact mul_nonneg h2 ENNReal.toReal_nonneg
  · exact mul_nonneg hz ENNReal.toReal_nonneg
