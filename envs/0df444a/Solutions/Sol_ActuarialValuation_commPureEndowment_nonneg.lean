-- Prove2me | solution 1 for ActuarialValuation.commPureEndowment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:55.971317+00:00
-- url     : https://prove2.me/submissions/efb1c4f9-dfc4-49dd-a750-9cd895f2fcf2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commTerminalLives
import Definitions.Def_actuarial_commPureEndowment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : 0 < commDiscountedLives l v x) (hT : 0 ≤ commTerminalLives l v x n) : 0 ≤ commPureEndowment l v x n := by
  unfold commPureEndowment
  exact div_nonneg hT (le_of_lt hD)
