-- Prove2me | solution 1 for ActuarialValuation.kmGreenwoodSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:36.627338+00:00
-- url     : https://prove2.me/submissions/7fb7486e-e787-4ab0-af4f-9d227affe9a9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_kmGreenwoodTerm
import Definitions.Def_actuarial_kmGreenwoodSum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ)
    (h : ∀ t ∈ Finset.range n, 0 ≤ kmGreenwoodTerm (d t) (r t)) :
    0 ≤ kmGreenwoodSum r d n := by
  unfold kmGreenwoodSum
  exact Finset.sum_nonneg fun t ht => h t ht
