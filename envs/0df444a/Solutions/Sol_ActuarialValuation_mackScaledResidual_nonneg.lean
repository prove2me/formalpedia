-- Prove2me | solution 1 for ActuarialValuation.mackScaledResidual_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:44.619982+00:00
-- url     : https://prove2.me/submissions/abab44ab-5d4a-4e9b-8aef-a324810f7337

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackScaledResidual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b exposure : ℝ) (h : 0 < exposure) : 0 ≤ mackScaledResidual a b exposure := by
  unfold mackScaledResidual mackSquaredResidual
  exact div_nonneg (sq_nonneg _) (le_of_lt h)
