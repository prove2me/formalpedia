-- Prove2me | solution 1 for ActuarialValuation.ratPortfolioPremium_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:38:23.115166+00:00
-- url     : https://prove2.me/submissions/fa534378-1073-4d15-aeaa-ad7d782f1f47

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ratPortfolioPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e r : ℕ → ℝ) (base : ℝ) : ratPortfolioPremium e r 0 base = 0 := by
  simp [ratPortfolioPremium]
