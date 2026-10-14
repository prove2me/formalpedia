-- Prove2me | solution 1 for ActuarialValuation.msExpectedBenefit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:12:38.270296+00:00
-- url     : https://prove2.me/submissions/a5e88d02-08cd-4b35-9ef7-ba7e67609afe

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msExpectedBenefit

import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p b : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i) (hb : ∀ i, 0 ≤ b i) : 0 ≤ msExpectedBenefit p b := by
  unfold msExpectedBenefit
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp i) (hb i)
