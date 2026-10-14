-- Prove2me | solution 1 for ActuarialValuation.svExp_model_distribution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:05:40.542061+00:00
-- url     : https://prove2.me/submissions/074aa134-6d39-4ac5-a1a6-25e8aab1655f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svCdf
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svExpSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (hT : Measurable T) (lambda t : ℝ) (hmodel : svSurvival μ T t = ENNReal.ofReal (svExpSurvival lambda t)) : svCdf μ T t + ENNReal.ofReal (svExpSurvival lambda t) = 1 := by
  rw [← hmodel]
  have hset : {ω | t < T ω} = ({ω | T ω ≤ t} : Set Ω)ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hmeas : MeasurableSet {ω | T ω ≤ t} := by
    change MeasurableSet (T ⁻¹' Set.Iic t)
    exact hT measurableSet_Iic
  unfold svCdf svSurvival
  rw [hset]
  rw [MeasureTheory.measure_add_measure_compl hmeas]
  simp
