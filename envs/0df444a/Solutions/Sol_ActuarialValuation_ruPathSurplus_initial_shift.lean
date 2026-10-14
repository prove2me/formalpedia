-- Prove2me | solution 1 for ActuarialValuation.ruPathSurplus_initial_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:27:44.947718+00:00
-- url     : https://prove2.me/submissions/3b1e0628-75ae-41f7-bef8-b8017b1a6c30

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ruPathSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u δ c : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ruPathSurplus (u+δ) c x n = ruPathSurplus u c x n+δ := by
  unfold ruPathSurplus
  ring
