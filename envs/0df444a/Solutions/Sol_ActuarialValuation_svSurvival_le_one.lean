-- Prove2me | solution 1 for ActuarialValuation.svSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:53:31.470304+00:00
-- url     : https://prove2.me/submissions/c22e8ae5-d6b3-43d9-9449-7a72c2f4b183

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (t : ℝ) : svSurvival μ T t ≤ 1 := by
  unfold svSurvival
  calc
    μ {ω | t < T ω} ≤ μ Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := by simp
