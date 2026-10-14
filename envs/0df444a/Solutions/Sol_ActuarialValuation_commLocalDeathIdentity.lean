-- Prove2me | solution 1 for ActuarialValuation.commLocalDeathIdentity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:26.831166+00:00
-- url     : https://prove2.me/submissions/6b455765-1515-4975-bbb8-569d7c4779cf

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commDiscountedLives
import Definitions.Def_actuarial_commDiscountedDeaths
import Definitions.Def_actuarial_commEffectiveDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commDiscountedDeaths l v x + commEffectiveDiscount v * commDiscountedLives l v x = commDiscountedLives l v x - commDiscountedLives l v (x+1) := by
  unfold commDiscountedDeaths commAnnualDeaths commEffectiveDiscount commDiscountedLives
  simp only [pow_succ]
  ring
