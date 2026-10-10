-- Prove2me | solution 1 for ActuarialValuation.dbTrancheResidualPension_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:38.397988+00:00
-- url     : https://prove2.me/submissions/714c16ec-f2a0-41ef-92d8-4e5b2ebf4922

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbTrancheResidualPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (pension reduction : ℕ → ℝ) (n : ℕ)
  (h : ∀ i ∈ Finset.range n, reduction i ≤ pension i) :
  0 ≤ dbTrancheResidualPension pension reduction n := by
  unfold dbTrancheResidualPension
  apply Finset.sum_nonneg
  intro i hi
  exact sub_nonneg.mpr (h i hi)
