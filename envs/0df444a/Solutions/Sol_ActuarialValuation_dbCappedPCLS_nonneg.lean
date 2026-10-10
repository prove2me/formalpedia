-- Prove2me | solution 1 for ActuarialValuation.dbCappedPCLS_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:32.915027+00:00
-- url     : https://prove2.me/submissions/38291d8a-bdcc-463b-b783-d1709d19bb5e

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCappedPCLS

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f A : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) (hA : 0 ≤ A) :
  0 ≤ dbCappedPCLS g f A := by
  unfold dbCappedPCLS dbHMRCMaximumCash
  apply le_min
  · apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 20) (le_of_lt hf)) hg
    · linarith
  · exact hA
