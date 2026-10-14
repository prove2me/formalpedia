-- Prove2me | solution 1 for ActuarialValuation.pvExpected_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:41.13158+00:00
-- url     : https://prove2.me/submissions/d0a010e6-c6a6-4ccd-9e7d-090357abdceb

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hl : ∀ i, 0 ≤ loss i) : 0 ≤ pvExpected p loss := by
  unfold pvExpected
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp i) (hl i)
