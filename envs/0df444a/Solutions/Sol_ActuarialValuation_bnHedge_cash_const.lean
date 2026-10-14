-- Prove2me | solution 1 for ActuarialValuation.bnHedge_cash_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:02:15.516894+00:00
-- url     : https://prove2.me/submissions/766c0b46-fdeb-47b5-9de1-4a194ecd6471

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnHedgeCash

import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u d R x : ℝ) (hud : u ≠ d) (hR : R ≠ 0) : bnHedgeCash R u d x x = x/R := by
  unfold bnHedgeCash
  field_simp [hR, sub_ne_zero.mpr hud] <;> ring
