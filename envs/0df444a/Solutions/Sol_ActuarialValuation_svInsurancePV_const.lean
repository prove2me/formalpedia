-- Prove2me | solution 1 for ActuarialValuation.svInsurancePV_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:14.255182+00:00
-- url     : https://prove2.me/submissions/e5a5db63-4d86-4c06-8c6c-95f589afecfc

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

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (r delta : ℝ) : svInsurancePresentValue μ (fun _ => r) delta = Real.exp (-delta*r) := by
  simp [svInsurancePresentValue]
