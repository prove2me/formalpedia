-- Prove2me | solution 1 for ActuarialValuation.cm1AccruedCARE_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:09:42.0913+00:00
-- url     : https://prove2.me/submissions/5e97ee77-d177-4517-adef-d97c52737545

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_cm1AccruedCARE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (salary revalue : ℕ → ℝ) (n : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (hs : ∀ t ∈ Finset.range n, 0 ≤ salary t)
    (hr : ∀ t ∈ Finset.range n, 0 ≤ revalue t) :
    0 ≤ cm1AccruedCARE salary revalue n a := by
  simp only [cm1AccruedCARE]
  exact mul_nonneg ha
    (Finset.sum_nonneg fun t ht => mul_nonneg (hs t ht) (hr t ht))
