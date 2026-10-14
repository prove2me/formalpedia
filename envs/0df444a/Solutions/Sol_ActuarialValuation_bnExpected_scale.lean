-- Prove2me | solution 1 for ActuarialValuation.bnExpected_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:51.672989+00:00
-- url     : https://prove2.me/submissions/1ae12dd8-505b-47a3-b28c-3a7ed05886b3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q x y a : ℝ) : bnExpectedPayoff q (a*x) (a*y) = a*bnExpectedPayoff q x y := by
  unfold bnExpectedPayoff
  ring
