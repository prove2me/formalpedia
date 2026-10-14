-- Prove2me | solution 1 for ActuarialValuation.msNetProfit_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:14:23.364251+00:00
-- url     : https://prove2.me/submissions/46e97c3b-c299-4d9f-b809-c058d79e4716

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msNetProfit

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p expenses cost : ℝ) : msNetProfit p expenses cost+expenses+cost = p := by
  unfold msNetProfit
  ring
