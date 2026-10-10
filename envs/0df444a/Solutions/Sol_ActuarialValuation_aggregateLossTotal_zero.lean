-- Prove2me | solution 1 for ActuarialValuation.aggregateLossTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:54:15.914974+00:00
-- url     : https://prove2.me/submissions/423db5a8-8c62-45a8-9793-92a05ec6cb0d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_aggregateLossTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) :
  aggregateLossTotal x 0 = 0 := by
  simp [aggregateLossTotal]
