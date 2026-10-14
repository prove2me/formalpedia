-- Prove2me | solution 1 for ActuarialValuation.csCauseOne_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:14:55.781987+00:00
-- url     : https://prove2.me/submissions/323529df-c7a0-4515-87e3-8d39e4bf2cfe

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_csCauseOne

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (U V Z : Ω → ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] :
    csCauseOne μ U V Z ≤ 1 := by
  unfold csCauseOne
  calc
    μ {ω | U ω < V ω ∧ U ω < Z ω} ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := by simp
