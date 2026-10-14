-- Prove2me | solution 1 for ActuarialValuation.bdCouponPV_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:37.798335+00:00
-- url     : https://prove2.me/submissions/e77b858d-6d08-4bea-a165-02394305a42f

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdCouponPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D c : ℕ → ℝ) (n : ℕ) : bdCouponPV D c (n+1) = bdCouponPV D c n + c n * D (n+1) := by
  unfold bdCouponPV
  exact Finset.sum_range_succ (fun k => c k * D (k+1)) n
