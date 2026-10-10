-- Prove2me | solution 1 for ActuarialValuation.dbCommutationHeadroom_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:18:27.196468+00:00
-- url     : https://prove2.me/submissions/17af27e9-c23b-4949-a92a-fd7b294159ef

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_dbCommutationHeadroom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (g f L₁ L₂ : ℝ)
  (hf : 0 < f) (h : L₁ ≤ L₂) :
  dbCommutationHeadroom g L₂ f ≤ dbCommutationHeadroom g L₁ f := by
  unfold dbCommutationHeadroom dbCommutedPension
  have hdiv : 0 ≤ (L₂ - L₁) / f := div_nonneg (sub_nonneg.mpr h) (le_of_lt hf)
  rw [sub_div] at hdiv
  linarith
