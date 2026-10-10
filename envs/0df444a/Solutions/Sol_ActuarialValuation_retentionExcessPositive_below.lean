-- Prove2me | solution 1 for ActuarialValuation.retentionExcessPositive_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:40.388513+00:00
-- url     : https://prove2.me/submissions/9734d152-8810-4904-a43e-21b01a32e50e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x d : ℝ) (h : x ≤ d) :
  retentionExcessPositive x d = 0 := by
  unfold retentionExcessPositive
  have hx : x - d ≤ 0 := sub_nonpos.mpr h
  exact max_eq_right hx
