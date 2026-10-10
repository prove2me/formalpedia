-- Prove2me | solution 1 for ActuarialValuation.cm1GrossLevelPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:56.087675+00:00
-- url     : https://prove2.me/submissions/ca02bfbe-1734-4ef1-8602-4972b68f2de2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1GrossLevelPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E A : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E) (hA : 0 < A) : 0 ≤ cm1GrossLevelPremium B E A := by
  unfold cm1GrossLevelPremium
  exact div_nonneg (add_nonneg hB hE) (le_of_lt hA)
