-- Prove2me | solution 1 for ActuarialValuation.bnExpected_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:29.924104+00:00
-- url     : https://prove2.me/submissions/cbab2276-313b-484b-b533-83561d34d3de

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnExpectedPayoff

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q x : ℝ) : bnExpectedPayoff q x x = x := by
  unfold bnExpectedPayoff
  ring
