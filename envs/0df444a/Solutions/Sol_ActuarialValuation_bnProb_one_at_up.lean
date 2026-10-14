-- Prove2me | solution 1 for ActuarialValuation.bnProb_one_at_up
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:57:45.605802+00:00
-- url     : https://prove2.me/submissions/c93015b6-f5c2-4f6c-a156-99e89ed43f9b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnRiskNeutralProb

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d : ℝ) (hud : u ≠ d) : bnRiskNeutralProb u d u = 1 := by
  unfold bnRiskNeutralProb
  field_simp [sub_ne_zero.mpr hud] <;> ring
