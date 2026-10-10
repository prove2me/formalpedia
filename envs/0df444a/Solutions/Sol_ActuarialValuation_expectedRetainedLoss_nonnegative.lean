-- Prove2me | solution 1 for ActuarialValuation.expectedRetainedLoss_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:56:04.724812+00:00
-- url     : https://prove2.me/submissions/d9125cfb-3f3b-4a6c-9e6a-a4dc095ee8cb

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hz : ∀ ω, 0 ≤ z ω) (ha : 0 ≤ a) :
    0 ≤ expectedRetainedLoss w z a := by
  classical
  change 0 ≤ ∑ ω : Ω, w ω * min (z ω) a
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (hw ω) (le_min (hz ω) ha)
