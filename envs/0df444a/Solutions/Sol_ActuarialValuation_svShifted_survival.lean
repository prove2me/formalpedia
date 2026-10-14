-- Prove2me | solution 1 for ActuarialValuation.svShifted_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:14.468992+00:00
-- url     : https://prove2.me/submissions/cfbe9f72-5262-4351-9a4f-2f4dc4e70e72

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvival
import Definitions.Def_actuarial_svShiftLifetime
import Mathlib.Tactic.Ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (s t : ℝ) : svSurvival μ (svShiftLifetime T s) t = svSurvival μ T (s+t) := by
  unfold svSurvival svShiftLifetime
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith
