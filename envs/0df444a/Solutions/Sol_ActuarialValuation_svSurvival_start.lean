-- Prove2me | solution 1 for ActuarialValuation.svSurvival_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:01.559147+00:00
-- url     : https://prove2.me/submissions/cedca9df-ed8b-42cd-ba5b-cccd9c8e6e02

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

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT0 : ∀ ω, 0 < T ω) : svSurvival μ T 0 = 1 := by
  have hall : {ω | (0 : ℝ) < T ω} = (Set.univ : Set Ω) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hT0 ω
  simp [svSurvival, hall]
