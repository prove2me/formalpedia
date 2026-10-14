-- Prove2me | solution 1 for ActuarialValuation.svInsurancePV_zero_interest
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:03.345088+00:00
-- url     : https://prove2.me/submissions/a546e481-8de8-4588-92f2-fce4245157dd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svInsurancePresentValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (T : Ω → ℝ) : svInsurancePresentValue μ T 0 = 1 := by
  simp [svInsurancePresentValue]
