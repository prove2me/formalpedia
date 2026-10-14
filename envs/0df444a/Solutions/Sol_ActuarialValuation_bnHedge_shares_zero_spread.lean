-- Prove2me | solution 1 for ActuarialValuation.bnHedge_shares_zero_spread
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:01:19.940278+00:00
-- url     : https://prove2.me/submissions/08fa3e28-9ed0-41da-8f0b-f0b4826c1ec2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bnHedgeShares

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (s u d x : ℝ) (hs : s ≠ 0) (hud : u ≠ d) : bnHedgeShares s u d x x = 0 := by
  unfold bnHedgeShares
  simp
