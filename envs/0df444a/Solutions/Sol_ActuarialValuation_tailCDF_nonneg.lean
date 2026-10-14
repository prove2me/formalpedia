-- Prove2me | solution 1 for ActuarialValuation.tailCDF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:13:47.032968+00:00
-- url     : https://prove2.me/submissions/a2b77a61-e966-4470-828d-23f601a3c577

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n t : ℕ)
    (hp : ∀ k ∈ Finset.range (n+1), 0 ≤ p k) :
    0 ≤ tailCDF p n t := by
  unfold tailCDF
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with h
  · exact hp k hk
  · exact le_refl 0
