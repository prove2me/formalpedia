-- Prove2me | solution 1 for ActuarialValuation.mackFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:34:54.964075+00:00
-- url     : https://prove2.me/submissions/c298d8ad-3410-47ae-8025-c59836a6a4ba

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackNumerator
import Definitions.Def_actuarial_mackDenominator
import Definitions.Def_actuarial_mackFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℕ → ℝ) (m j : ℕ) (hn : 0 ≤ mackNumerator c m j) (hd : 0 < mackDenominator c m j) : 0 ≤ mackFactor c m j := by
  unfold mackFactor
  exact div_nonneg hn (le_of_lt hd)
