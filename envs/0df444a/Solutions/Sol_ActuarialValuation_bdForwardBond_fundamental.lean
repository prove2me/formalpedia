-- Prove2me | solution 1 for ActuarialValuation.bdForwardBond_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:09.547103+00:00
-- url     : https://prove2.me/submissions/5dd01549-58b8-48c7-ad82-6ceb81e2f01c

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardDiscount
import Definitions.Def_actuarial_bdForwardBond
import Definitions.Def_actuarial_bdZeroPrice
import Definitions.Def_actuarial_bdForwardGross

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (s u t : ℕ) (face : ℝ) (hs : D s ≠ 0) (hu : D u ≠ 0) (ht : D t ≠ 0) : (bdForwardDiscount D s u * bdForwardDiscount D u t = bdForwardDiscount D s t) ∧ (bdForwardBond D face s t * D s = bdZeroPrice D face t) ∧ (bdForwardGross D s t * bdForwardDiscount D s t = 1) := by
  constructor
  · unfold bdForwardDiscount
    field_simp [hs, hu] <;> ring
  constructor
  · unfold bdForwardBond bdForwardDiscount bdZeroPrice
    field_simp [hs] <;> ring
  · unfold bdForwardGross bdForwardDiscount
    field_simp [hs, ht] <;> ring
