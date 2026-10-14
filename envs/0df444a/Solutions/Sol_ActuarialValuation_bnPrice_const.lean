-- Prove2me | solution 1 for ActuarialValuation.bnPrice_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:15.153766+00:00
-- url     : https://prove2.me/submissions/62ccd106-01a8-4f2f-9245-3b362fd671e8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnOnePeriodPrice

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R q x : ℝ) : bnOnePeriodPrice R q x x = x/R := by
  unfold bnOnePeriodPrice bnExpectedPayoff
  ring
