-- Prove2me | solution 1 for ActuarialValuation.csJointSurvival_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:21:03.633508+00:00
-- url     : https://prove2.me/submissions/f2e28e40-f668-4f6a-a2db-c05faeb8015a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csJointSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] (s t : ℝ) :
    csJointSurvival μ U V Z s t ≤ 1 := by
  calc
    csJointSurvival μ U V Z s t ≤ μ Set.univ := by
      unfold csJointSurvival
      exact measure_mono (Set.subset_univ _)
    _ = 1 := by simp
