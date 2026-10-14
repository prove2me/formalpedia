-- Prove2me | solution 1 for ActuarialValuation.srRuinProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:23:31.996575+00:00
-- url     : https://prove2.me/submissions/4f019222-19de-44d5-bd36-de7cd1bff983

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (u c : ℝ) (W Y : ℕ → Ω → ℝ) : 0≤srRuinProbability μ u c W Y := by
  unfold srRuinProbability
  exact ENNReal.toReal_nonneg
