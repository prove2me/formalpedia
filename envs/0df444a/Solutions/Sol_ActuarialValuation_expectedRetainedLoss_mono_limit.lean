-- Prove2me | solution 1 for ActuarialValuation.expectedRetainedLoss_mono_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T14:56:10.559003+00:00
-- url     : https://prove2.me/submissions/deb5d4a4-6971-414c-83b6-d83be8711e6b

import Mathlib
import Definitions.Def_actuarial_expectedRetainedLoss
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a b : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hab : a ≤ b) :
    expectedRetainedLoss w z a ≤ expectedRetainedLoss w z b := by
  classical
  change (∑ ω : Ω, w ω * min (z ω) a) ≤
    (∑ ω : Ω, w ω * min (z ω) b)
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (min_le_min_left (z ω) hab) (hw ω)
