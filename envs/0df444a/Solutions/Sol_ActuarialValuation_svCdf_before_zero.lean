-- Prove2me | solution 1 for ActuarialValuation.svCdf_before_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:48:40.624214+00:00
-- url     : https://prove2.me/submissions/72a7ed24-f53f-4153-880c-8269ab8f9953

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

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT0 : ∀ ω, 0 ≤ T ω) (t : ℝ) (ht : t < 0) : svCdf μ T t = 0 := by
  have hempty : {ω | T ω ≤ t} = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr (lt_of_lt_of_le ht (hT0 ω))
  simp [svCdf, hempty]
