-- Prove2me | solution 1 for ActuarialValuation.bdCouponPV_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:48.590911+00:00
-- url     : https://prove2.me/submissions/60de55e8-870d-4028-ace9-5c4fe2378abb

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D a b : ℕ → ℝ) (n : ℕ) : bdCouponPV D (fun k => a k+b k) n = bdCouponPV D a n + bdCouponPV D b n := by
  unfold bdCouponPV
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring
