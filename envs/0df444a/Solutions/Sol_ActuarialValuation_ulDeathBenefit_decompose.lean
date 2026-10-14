-- Prove2me | solution 1 for ActuarialValuation.ulDeathBenefit_decompose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:21:24.355991+00:00
-- url     : https://prove2.me/submissions/b2fbfebe-9b20-4cc2-94cc-407e62906779

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulDeathBenefit
import Definitions.Def_actuarial_ulNetAmountAtRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (fund guarantee : ℝ) : ulDeathBenefit fund guarantee=fund+ulNetAmountAtRisk fund guarantee := by
  unfold ulDeathBenefit ulNetAmountAtRisk
  rcases le_total guarantee fund with h | h
  · rw [max_eq_left h, max_eq_left (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
    ring
