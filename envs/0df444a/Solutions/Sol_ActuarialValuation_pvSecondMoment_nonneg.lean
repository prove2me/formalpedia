-- Prove2me | solution 1 for ActuarialValuation.pvSecondMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:53.728867+00:00
-- url     : https://prove2.me/submissions/7e08a394-e345-454c-ae39-5331c480c6a3

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvSecondMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ pvSecondMoment p loss := by
  unfold pvSecondMoment
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp i) (sq_nonneg (loss i))
