-- Prove2me | solution 1 for ActuarialValuation.irAvgCost_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:03:43.649986+00:00
-- url     : https://prove2.me/submissions/0feec801-39f8-4abb-a7a7-b2ac284128c4

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irAvgCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (cost count : ℝ) (h : count≠0) : irAvgCost cost count*count=cost := by
  unfold irAvgCost
  field_simp [h]
