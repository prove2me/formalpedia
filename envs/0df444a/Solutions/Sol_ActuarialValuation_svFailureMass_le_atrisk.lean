-- Prove2me | solution 1 for ActuarialValuation.svFailureMass_le_atrisk
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:31.508814+00:00
-- url     : https://prove2.me/submissions/66cf7808-4a0d-42da-8f6a-9a74c5c153e1

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFailureMass
import Definitions.Def_actuarial_svSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : Ω → ℝ) (k : ℕ) (hk : 0 < k) : svFailureMass μ T k ≤ svSurvival μ T ((k:ℝ)-1) := by
  unfold svFailureMass svSurvival
  apply MeasureTheory.measure_mono
  intro ω hω
  change ((k : ℝ) - 1) < T ω
  change T ω = (k : ℝ) at hω
  rw [hω]
  linarith
