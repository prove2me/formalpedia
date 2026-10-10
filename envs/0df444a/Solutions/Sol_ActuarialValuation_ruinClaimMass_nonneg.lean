-- Prove2me | solution 1 for ActuarialValuation.ruinClaimMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T06:43:47.389441+00:00
-- url     : https://prove2.me/submissions/8ba0e506-7514-4f2d-b192-b55aad4bb765

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ruinClaimMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (B : ℕ)
  (hw : ∀ k, 0 ≤ w k) : 0 ≤ ruinClaimMass w B := by
  unfold ruinClaimMass
  apply Finset.sum_nonneg
  intro k hk
  exact hw k
