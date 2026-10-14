-- Prove2me | solution 1 for ActuarialValuation.ruDeficit_zero_if_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:21:59.603109+00:00
-- url     : https://prove2.me/submissions/19f4bdea-8071-439e-bce5-eba628b03171

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruDeficit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ)
    (h : 0 ≤ ruPathSurplus u c x n) :
    ruDeficit u c x n = 0 := by
  unfold ruDeficit
  exact max_eq_left (neg_nonpos.mpr h)
