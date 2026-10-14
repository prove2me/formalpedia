-- Prove2me | solution 1 for ActuarialValuation.bnExpected_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:40.448986+00:00
-- url     : https://prove2.me/submissions/cacda7e3-3699-41ef-86eb-078526c39b04

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q x1 y1 x2 y2 : ℝ) : bnExpectedPayoff q (x1+x2) (y1+y2) = bnExpectedPayoff q x1 y1 + bnExpectedPayoff q x2 y2 := by
  unfold bnExpectedPayoff
  ring
