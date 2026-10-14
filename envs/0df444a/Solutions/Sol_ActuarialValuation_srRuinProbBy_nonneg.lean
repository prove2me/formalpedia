-- Prove2me | solution 1 for ActuarialValuation.srRuinProbBy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:41:35.802715+00:00
-- url     : https://prove2.me/submissions/adfc15bf-e2bc-4d55-a80f-6cb9658e10e1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinProbabilityBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) : 0≤srRuinProbabilityBy μ u c W Y N := by
  unfold srRuinProbabilityBy
  exact ENNReal.toReal_nonneg
