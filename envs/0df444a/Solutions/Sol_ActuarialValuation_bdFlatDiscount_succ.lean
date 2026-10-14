-- Prove2me | solution 1 for ActuarialValuation.bdFlatDiscount_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:02:17.196969+00:00
-- url     : https://prove2.me/submissions/9f54071c-27fc-4cfc-8f62-1e2ba1751e2c

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdFlatDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R : ℝ) (t : ℕ) (h : R ≠ 0) : bdFlatDiscount R (t+1) * R = bdFlatDiscount R t := by
  unfold bdFlatDiscount
  rw [pow_succ]
  field_simp [h] <;> ring
