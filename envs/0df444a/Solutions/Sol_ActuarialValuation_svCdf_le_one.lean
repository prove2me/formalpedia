-- Prove2me | solution 1 for ActuarialValuation.svCdf_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:32.514973+00:00
-- url     : https://prove2.me/submissions/7a3e93cd-99a3-476f-b623-ae66df4fcffd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (t : ℝ) : svCdf μ T t ≤ 1 := by
  unfold svCdf
  calc
    μ {ω | T ω ≤ t} ≤ μ Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := by simp
