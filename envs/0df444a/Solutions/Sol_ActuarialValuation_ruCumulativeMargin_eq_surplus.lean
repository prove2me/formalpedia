-- Prove2me | solution 1 for ActuarialValuation.ruCumulativeMargin_eq_surplus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:29:28.372218+00:00
-- url     : https://prove2.me/submissions/2dfa327a-4a3f-4b4e-b291-81a8e00bca3d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruCumulativeMargin
import Definitions.Def_actuarial_ruPathSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruCumulativeMargin u c x n = ruPathSurplus u c x n := by
  unfold ruCumulativeMargin ruPathSurplus
  ring
