-- Prove2me | solution 1 for ActuarialValuation.bdForwardDiscount_reconstruct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:56:52.225083+00:00
-- url     : https://prove2.me/submissions/c83e005f-8e81-4de2-ad1e-3f7559ccc25e

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

theorem solution (D : ℕ → ℝ) (s t : ℕ) (hs : D s ≠ 0) : bdForwardDiscount D s t * D s = D t := by
  unfold bdForwardDiscount
  field_simp [hs] <;> ring
