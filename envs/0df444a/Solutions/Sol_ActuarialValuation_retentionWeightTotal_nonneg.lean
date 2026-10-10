-- Prove2me | solution 1 for ActuarialValuation.retentionWeightTotal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:04:12.678974+00:00
-- url     : https://prove2.me/submissions/ecd802f3-37be-43e5-a9ad-777faf2e25ef

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionWeightTotal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (B : ℕ) (hw : ∀ s, 0 ≤ w s) :
  0 ≤ retentionWeightTotal w B := by
  unfold retentionWeightTotal
  exact Finset.sum_nonneg (fun s hs => hw s)
