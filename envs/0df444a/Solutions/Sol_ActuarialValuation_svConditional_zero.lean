-- Prove2me | solution 1 for ActuarialValuation.svConditional_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:32.781485+00:00
-- url     : https://prove2.me/submissions/d269ad52-3d83-4c3f-a645-2df442b564bd

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svConditionalSurvival
import Definitions.Def_actuarial_svSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s : ℝ) (h0 : svSurvival μ T s ≠ 0) (hfin : svSurvival μ T s ≠ ⊤) : svConditionalSurvival μ T s 0 = 1 := by
  unfold svConditionalSurvival
  simp only [add_zero]
  exact ENNReal.div_self h0 hfin
