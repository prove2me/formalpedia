-- Prove2me | solution 1 for ActuarialValuation.bdForwardDiscount_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:41.476127+00:00
-- url     : https://prove2.me/submissions/2997b3e5-4408-46d4-a8ab-b35f0046d35d

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (s u t : ℕ) (hs : D s ≠ 0) (hu : D u ≠ 0) : bdForwardDiscount D s u * bdForwardDiscount D u t = bdForwardDiscount D s t := by
  unfold bdForwardDiscount
  field_simp [hs, hu] <;> ring
