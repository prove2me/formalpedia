-- Prove2me | solution 1 for ActuarialValuation.retentionExcessPositive_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:48.091161+00:00
-- url     : https://prove2.me/submissions/5366766d-3721-41a7-8852-49056b2421c3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℝ) :
  0 ≤ retentionExcessPositive x d := by
  unfold retentionExcessPositive
  exact le_max_right _ _
