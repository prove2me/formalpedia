-- Prove2me | solution 1 for ActuarialValuation.pucNormalCost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:18:17.109051+00:00
-- url     : https://prove2.me/submissions/87bc0819-75cb-44e9-9db2-abc2b7caedc7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucNormalCost

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) (f : ℝ) (hu : 0 ≤ u n) (hf : 0 ≤ f) : 0 ≤ pucNormalCost u n f := by
  unfold pucNormalCost
  exact mul_nonneg hu hf
