-- Prove2me | solution 1 for ActuarialValuation.retentionExcessPositive_mono_retention
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:56:57.322351+00:00
-- url     : https://prove2.me/submissions/8379f100-1d02-4b7f-9f13-14d17f39ba84

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_retentionExcessPositive
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (x a b : ℝ) (h : a ≤ b) :
  retentionExcessPositive x b ≤ retentionExcessPositive x a := by
  unfold retentionExcessPositive
  exact max_le_max (by linarith) (le_refl _)
