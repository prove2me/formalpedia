-- Prove2me | solution 1 for ActuarialValuation.kmRestrictedLife_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:19.917711+00:00
-- url     : https://prove2.me/submissions/3e032fe9-e196-4ab9-89bc-86d11d149213

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmRestrictedLife

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ)
    (h : ∀ t ∈ Finset.range n, 0 ≤ kmSurvival r d t) :
    0 ≤ kmRestrictedLife r d n := by
  unfold kmRestrictedLife
  exact Finset.sum_nonneg fun t ht => h t ht
