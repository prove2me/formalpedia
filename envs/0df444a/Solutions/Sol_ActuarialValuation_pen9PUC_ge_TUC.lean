-- Prove2me | solution 1 for ActuarialValuation.pen9PUC_ge_TUC
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:25:31.631889+00:00
-- url     : https://prove2.me/submissions/238482d7-1c80-4275-ad67-2da491cca88d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9TUC

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a current projected f : ℝ) (n : ℕ) (ha : 0 ≤ a) (hf : 0 ≤ f) (hpay : current ≤ projected) : pen9TUC a current f n ≤ pen9PUC a projected f n := by
  unfold pen9TUC pen9PUC
  apply mul_le_mul_of_nonneg_right _ hf
  exact mul_le_mul_of_nonneg_left hpay
    (mul_nonneg ha (Nat.cast_nonneg n))
