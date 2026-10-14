-- Prove2me | solution 1 for ActuarialValuation.pvTerm_after_expiry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:54:50.441404+00:00
-- url     : https://prove2.me/submissions/38875525-e44b-432f-a6b2-b52351cf31ae

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvTermBenefit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (benefit discount : ℕ → ℝ) (term k : ℕ) (h : term ≤ k) : pvTermBenefit benefit discount term k = 0 := by
  simp [pvTermBenefit, not_lt.mpr h]
