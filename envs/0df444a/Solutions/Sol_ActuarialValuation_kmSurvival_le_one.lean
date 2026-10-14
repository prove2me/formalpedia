-- Prove2me | solution 1 for ActuarialValuation.kmSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:31:22.728777+00:00
-- url     : https://prove2.me/submissions/267d4741-11e9-4b02-a796-e2ebcc03352a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Definitions.Def_actuarial_kmSurvivalFactor
import Definitions.Def_actuarial_kmSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ)
    (h : ∀ t ∈ Finset.range n,
      0 ≤ kmSurvivalFactor (d t) (r t) ∧ kmSurvivalFactor (d t) (r t) ≤ 1) :
    kmSurvival r d n ≤ 1 := by
  unfold kmSurvival
  apply Finset.prod_le_one
  · intro t ht
    exact (h t ht).1
  · intro t ht
    exact (h t ht).2
