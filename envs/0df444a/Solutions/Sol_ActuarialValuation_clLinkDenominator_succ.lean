-- Prove2me | solution 1 for ActuarialValuation.clLinkDenominator_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:22:57.117883+00:00
-- url     : https://prove2.me/submissions/fb636a43-a168-45be-8dfa-6309cfada5e8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkDenominator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (m j : ℕ) : clLinkDenominator p (m+1) j = clLinkDenominator p m j + p m j := by
  simp [clLinkDenominator, Finset.sum_range_succ]
