-- Prove2me | solution 1 for ActuarialValuation.ruSurplus_premium_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:28:07.379987+00:00
-- url     : https://prove2.me/submissions/ac3c9012-1326-4772-9e8a-16ed25eb1928

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruPathSurplus
import Definitions.Def_actuarial_ruPremiumTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c δ : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruPathSurplus u (c+δ) x n =
      ruPathSurplus u c x n + (n:ℝ)*δ := by
  unfold ruPathSurplus ruPremiumTotal
  ring
