-- Prove2me | solution 1 for ActuarialValuation.svSurvivalHazardInsurance_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:10:49.612996+00:00
-- url     : https://prove2.me/submissions/8e343265-bf7e-4c9c-9144-e38e04baa93c

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svCdf
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svExpSurvival
import Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
import Definitions.Def_actuarial_svExpCumulativeHazard
import Definitions.Def_actuarial_svInsurancePresentValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (T : Ω → ℝ) (hT : Measurable T) (t lambda : ℝ) (hmodel : svSurvival μ T t = ENNReal.ofReal (svExpSurvival lambda t)) : (svCdf μ T t + ENNReal.ofReal (svExpSurvival lambda t) = 1) ∧ (svSurvivalFromCumulativeHazard (svExpCumulativeHazard lambda t) = svExpSurvival lambda t) ∧ (svInsurancePresentValue μ T 0 = 1) := by
  have hdist : svCdf μ T t + ENNReal.ofReal (svExpSurvival lambda t) = 1 := by
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
  have hexp : svSurvivalFromCumulativeHazard (svExpCumulativeHazard lambda t) =
      svExpSurvival lambda t := by
    unfold svSurvivalFromCumulativeHazard svExpCumulativeHazard svExpSurvival
    congr 1
    ring
  have hpv : svInsurancePresentValue μ T 0 = 1 := by
    simp [svInsurancePresentValue]
  exact ⟨hdist, hexp, hpv⟩
