-- Prove2me | solution 1 for ActuarialValuation.cm1ExpectedBenefitPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:23:28.297524+00:00
-- url     : https://prove2.me/submissions/32a465ee-1026-4c25-a325-71de95fde9ab

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedBenefitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (b d p : ℕ → ℝ) (N : ℕ) (hb : ∀ t ∈ Finset.range N, 0 ≤ b t) (hd : ∀ t ∈ Finset.range N, 0 ≤ d t) (hp : ∀ t ∈ Finset.range N, 0 ≤ p t) : 0 ≤ cm1ExpectedBenefitPV b d p N := by
  unfold cm1ExpectedBenefitPV
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (mul_nonneg (hb t ht) (hd t ht)) (hp t ht)
