-- Prove2me | solution 1 for ActuarialValuation.svDiscreteHazard_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:07:59.751454+00:00
-- url     : https://prove2.me/submissions/3e90181a-2fec-4c5c-926b-cb8067db2c30

import Mathlib.Tactic.Linarith
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svDiscreteHazard
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svFailureMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ) (hk : 0 < k) (hs : svSurvival μ T ((k:ℝ)-1) ≠ 0) : svDiscreteHazard μ T k ≤ 1 := by
  have hmass : svFailureMass μ T k ≤ svSurvival μ T ((k:ℝ)-1) := by
    unfold svFailureMass svSurvival
    apply MeasureTheory.measure_mono
    intro ω hω
    change ((k : ℝ) - 1) < T ω
    change T ω = (k : ℝ) at hω
    rw [hω]
    linarith
  have hbound : svSurvival μ T ((k:ℝ)-1) ≤ (1 : ENNReal) := by
    unfold svSurvival
    calc
      μ {ω | ((k : ℝ) - 1) < T ω} ≤ μ Set.univ :=
        MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hfin : svSurvival μ T ((k:ℝ)-1) ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤) hbound
  unfold svDiscreteHazard
  apply (ENNReal.div_le_iff_le_mul (Or.inl hs) (Or.inl hfin)).2
  simpa only [one_mul] using hmass
