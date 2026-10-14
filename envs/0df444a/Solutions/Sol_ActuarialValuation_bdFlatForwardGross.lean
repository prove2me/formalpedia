-- Prove2me | solution 1 for ActuarialValuation.bdFlatForwardGross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:02:29.012309+00:00
-- url     : https://prove2.me/submissions/43d9e341-4c88-46e9-9a71-00e8576adb7b

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardGross
import Definitions.Def_actuarial_bdFlatDiscount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R : ℝ) (t : ℕ) (hR : R ≠ 0) : bdForwardGross (bdFlatDiscount R) t (t+1) = R := by
  unfold bdForwardGross bdFlatDiscount
  rw [pow_succ]
  field_simp [hR] <;> ring
