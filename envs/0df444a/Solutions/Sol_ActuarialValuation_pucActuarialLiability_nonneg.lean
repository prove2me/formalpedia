-- Prove2me | solution 1 for ActuarialValuation.pucActuarialLiability_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:31:13.839155+00:00
-- url     : https://prove2.me/submissions/b7dabe2a-d981-4a66-8910-8dcb8448a9b1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucAccruedBenefit
import Definitions.Def_actuarial_pucActuarialLiability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (u : ℕ → ℝ) (n : ℕ) (f : ℝ) (hu : 0 ≤ pucAccruedBenefit u n) (hf : 0 ≤ f) : 0 ≤ pucActuarialLiability u n f := by
  unfold pucActuarialLiability
  exact mul_nonneg hu hf
