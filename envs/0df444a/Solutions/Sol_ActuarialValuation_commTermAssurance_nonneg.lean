-- Prove2me | solution 1 for ActuarialValuation.commTermAssurance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:44.434986+00:00
-- url     : https://prove2.me/submissions/e8537ce7-7cad-4246-a29f-460abfa34180

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commDeathSum
import Definitions.Def_actuarial_commTermAssurance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x n : ℕ) (hD : 0 < commDiscountedLives l v x) (hM : 0 ≤ commDeathSum l v x n) : 0 ≤ commTermAssurance l v x n := by
  unfold commTermAssurance
  exact div_nonneg hM (le_of_lt hD)
