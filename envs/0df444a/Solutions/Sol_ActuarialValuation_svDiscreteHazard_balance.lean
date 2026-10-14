-- Prove2me | solution 1 for ActuarialValuation.svDiscreteHazard_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:04:44.054+00:00
-- url     : https://prove2.me/submissions/a00cbe44-45ee-4d92-aebf-2e37a8e216af

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

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) (h0 : svSurvival μ T ((k:ℝ)-1) ≠ 0) (hfin : svSurvival μ T ((k:ℝ)-1) ≠ ⊤) : svDiscreteHazard μ T k * svSurvival μ T ((k:ℝ)-1) = svFailureMass μ T k := by
  unfold svDiscreteHazard
  exact ENNReal.div_mul_cancel h0 hfin
