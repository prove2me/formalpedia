-- Prove2me | solution 1 for ActuarialValuation.dbHMRCMaximumCash_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:12.227994+00:00
-- url     : https://prove2.me/submissions/a99248d9-d50b-4114-bc52-262bd855e491

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbHMRCMaximumCash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f : ℝ)
  (hg : 0 ≤ g) (hf : 0 < f) : 0 ≤ dbHMRCMaximumCash g f := by
  unfold dbHMRCMaximumCash
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 20) (le_of_lt hf)) hg
  · linarith
