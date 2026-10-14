-- Prove2me | solution 1 for ActuarialValuation.svConditional_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:29.761038+00:00
-- url     : https://prove2.me/submissions/a0dfd450-3acf-4e4b-9b6f-daac7546e729

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

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) (h0 : svSurvival μ T s ≠ 0) (hfin : svSurvival μ T s ≠ ⊤) : svConditionalSurvival μ T s t * svSurvival μ T s = svSurvival μ T (s+t) := by
  unfold svConditionalSurvival
  exact ENNReal.div_mul_cancel h0 hfin
