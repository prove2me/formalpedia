-- Prove2me | solution 1 for ActuarialValuation.bdParCoupon_price_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:59:32.616008+00:00
-- url     : https://prove2.me/submissions/1d2eefc4-7031-481c-a52f-1fc7b6b53869

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdParCoupon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (n : ℕ) (ha : (∑ k∈Finset.range n, D (k+1)) ≠ 0) : bdParCoupon D n * (∑ k∈Finset.range n, D (k+1)) + D n = 1 := by
  unfold bdParCoupon
  field_simp [ha] <;> ring
