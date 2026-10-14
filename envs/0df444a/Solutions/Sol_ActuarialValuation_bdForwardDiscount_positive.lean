-- Prove2me | solution 1 for ActuarialValuation.bdForwardDiscount_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:30.496945+00:00
-- url     : https://prove2.me/submissions/6a516731-347c-4c38-a841-8d41204e0d9d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (s t : ℕ) (hs : 0 < D s) (ht : 0 < D t) : 0 < bdForwardDiscount D s t := by
  unfold bdForwardDiscount
  exact div_pos ht hs
