-- Prove2me | solution 1 for ActuarialValuation.ratClaimsSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:27:20.027983+00:00
-- url     : https://prove2.me/submissions/37bf417a-220b-4074-8812-9bcdcd3dbf6e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_ratClaimsSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (n : ℕ)
    (hl : ∀ i ∈ Finset.range n, 0 ≤ l i) :
    0 ≤ ratClaimsSum l n := by
  unfold ratClaimsSum
  exact Finset.sum_nonneg fun i hi => hl i hi
