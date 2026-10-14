-- Prove2me | solution 1 for ActuarialValuation.tailUpperMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:19.874971+00:00
-- url     : https://prove2.me/submissions/cf534576-ede9-4798-a324-662c4f48684d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailUpperMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n t : ℕ)
    (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    0 ≤ tailUpperMass p n t := by
  unfold tailUpperMass
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with h
  · exact hp k hk
  · exact le_refl 0
