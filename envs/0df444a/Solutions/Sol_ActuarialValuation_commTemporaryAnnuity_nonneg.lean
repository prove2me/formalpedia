-- Prove2me | solution 1 for ActuarialValuation.commTemporaryAnnuity_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:31.161487+00:00
-- url     : https://prove2.me/submissions/3914fbd7-a012-4cfe-87bb-bc6ca5fa99ca

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commSurvivorSum
import Definitions.Def_actuarial_commTemporaryAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : 0 < commDiscountedLives l v x) (hN : 0 ≤ commSurvivorSum l v x n) : 0 ≤ commTemporaryAnnuity l v x n := by
  unfold commTemporaryAnnuity
  exact div_nonneg hN (le_of_lt hD)
