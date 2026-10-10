-- Prove2me | solution 1 for ActuarialValuation.cm1MortalityProfit_favourable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:59.926898+00:00
-- url     : https://prove2.me/submissions/2f5ace8b-8e78-43a7-b93e-ce9b2c91286b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1MortalityProfit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e a S : ℝ) (h : a ≤ e) (hS : 0 ≤ S) : 0 ≤ cm1MortalityProfit e a S := by
  unfold cm1MortalityProfit
  exact mul_nonneg (sub_nonneg.mpr h) hS
