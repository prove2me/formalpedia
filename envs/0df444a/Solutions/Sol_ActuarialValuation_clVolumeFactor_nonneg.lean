-- Prove2me | solution 1 for ActuarialValuation.clVolumeFactor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:29:39.563672+00:00
-- url     : https://prove2.me/submissions/b97b395c-34bd-4f36-9567-fde2ee6e00d0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator
import Definitions.Def_actuarial_clVolumeFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (m j : ℕ) (hN : 0 ≤ clLinkNumerator p m j) (hD : 0 < clLinkDenominator p m j) : 0 ≤ clVolumeFactor p m j := by
  change 0 ≤ clLinkNumerator p m j / clLinkDenominator p m j
  exact div_nonneg hN (le_of_lt hD)
