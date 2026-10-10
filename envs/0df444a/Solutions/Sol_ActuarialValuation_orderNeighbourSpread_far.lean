-- Prove2me | solution 1 for ActuarialValuation.orderNeighbourSpread_far
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:46:23.613314+00:00
-- url     : https://prove2.me/submissions/73111c23-7907-4a95-b0be-ee5be3133517

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_orderNeighbourSpread
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


open ActuarialValuation

theorem solution (w : ℕ → ℝ) (c s : ℕ) (delta : ℝ)
  (ha : s + 1 ≠ c) (hb : s ≠ c + 1) (hc : s ≠ c) :
  orderNeighbourSpread w c delta s = w s := by
  show w s + (if s + 1 = c then delta / 2 else 0) +
      (if s = c + 1 then delta / 2 else 0) -
      (if s = c then delta else 0) = w s
  rw [if_neg ha, if_neg hb, if_neg hc]
  simp
