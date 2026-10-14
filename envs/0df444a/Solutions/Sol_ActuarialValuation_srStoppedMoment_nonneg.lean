-- Prove2me | solution 1 for ActuarialValuation.srStoppedMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:37:20.506367+00:00
-- url     : https://prove2.me/submissions/d7aa6373-c368-4e08-9bd5-f114203376a3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_srStoppedMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) : 0≤srStoppedMoment μ R u c W Y N := by
  unfold srStoppedMoment
  apply MeasureTheory.integral_nonneg
  intro ω
  dsimp [srStoppedExp, srExpLoss]
  positivity
  -- Replace the marker above with a complete proof before lint-submit.
