-- Prove2me | solution 1 for ActuarialValuation.aggregateDeductibleCeded_monotone_deductible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:02:37.409919+00:00
-- url     : https://prove2.me/submissions/1500b627-8b8c-4114-bb01-068204a344d2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Definitions.Def_actuarial_aggregateDeductibleCeded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x : ℕ → ℕ) (n d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
  aggregateDeductibleCeded x n d₂ ≤ aggregateDeductibleCeded x n d₁ := by
  change aggregateLossTotal x n - d₂ ≤ aggregateLossTotal x n - d₁
  omega
