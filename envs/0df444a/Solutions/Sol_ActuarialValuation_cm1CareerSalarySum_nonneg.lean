-- Prove2me | solution 1 for ActuarialValuation.cm1CareerSalarySum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:18:28.951981+00:00
-- url     : https://prove2.me/submissions/db802983-79e2-4a53-a882-ca8acbce046e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_cm1CareerSalarySum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary : ℕ → ℝ) (n : ℕ)
    (hs : ∀ t ∈ Finset.range n, 0 ≤ salary t) :
    0 ≤ cm1CareerSalarySum salary n := by
  simp only [cm1CareerSalarySum]
  exact Finset.sum_nonneg fun t ht => hs t ht
