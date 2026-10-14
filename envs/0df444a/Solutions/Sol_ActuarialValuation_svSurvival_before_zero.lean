-- Prove2me | solution 1 for ActuarialValuation.svSurvival_before_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:45.921044+00:00
-- url     : https://prove2.me/submissions/131d596e-0d9d-4dff-8cdf-2a3d3535f884

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvival
import Mathlib.Tactic.Ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT0 : ∀ ω, 0 ≤ T ω) (t : ℝ) (ht : t < 0) : svSurvival μ T t = 1 := by
  have hall : {ω | t < T ω} = (Set.univ : Set Ω) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact lt_of_lt_of_le ht (hT0 ω)
  simp [svSurvival, hall]
