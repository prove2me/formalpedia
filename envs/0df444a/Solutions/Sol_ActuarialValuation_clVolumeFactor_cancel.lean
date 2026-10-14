-- Prove2me | solution 1 for ActuarialValuation.clVolumeFactor_cancel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:30:57.595993+00:00
-- url     : https://prove2.me/submissions/19326d91-49e3-45d7-9471-9ba7425dbdd0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator
import Definitions.Def_actuarial_clVolumeFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (m j : ℕ) (h : clLinkDenominator p m j ≠ 0) : clVolumeFactor p m j * clLinkDenominator p m j = clLinkNumerator p m j := by
  change (clLinkNumerator p m j / clLinkDenominator p m j) *
    clLinkDenominator p m j = clLinkNumerator p m j
  exact (eq_div_iff h).mp rfl
