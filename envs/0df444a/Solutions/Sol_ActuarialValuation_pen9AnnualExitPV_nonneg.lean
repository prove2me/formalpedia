-- Prove2me | solution 1 for ActuarialValuation.pen9AnnualExitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:06:44.067197+00:00
-- url     : https://prove2.me/submissions/1ece1b13-d4d8-49df-bb78-2a4d82a6c7fa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AnnualExitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p v b : ℕ → ℝ) (n : ℕ) (hp : ∀ t ∈ Finset.range n, 0 ≤ p t) (hv : ∀ t ∈ Finset.range n, 0 ≤ v t) (hb : ∀ t ∈ Finset.range n, 0 ≤ b t) : 0 ≤ pen9AnnualExitPV p v b n := by
  unfold pen9AnnualExitPV
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hp t ht) (hv t ht)) (hb t ht)
