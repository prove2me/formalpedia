-- Prove2me | solution 1 for ActuarialValuation.clPaidFraction_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:28:51.726606+00:00
-- url     : https://prove2.me/submissions/0b91b714-3d60-4700-a433-571d5ccc5d70

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidFraction
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℝ) (h : f ≠ 0) : clPaidFraction f * f = 1 := by
  change (1 : ℝ) / f * f = 1
  field_simp [h]
