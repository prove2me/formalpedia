-- Prove2me | solution 1 for ActuarialValuation.bdForwardBond_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:57:26.255715+00:00
-- url     : https://prove2.me/submissions/03949b27-776c-4b9e-93d9-26baaca8a8fc

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdForwardBond
import Definitions.Def_actuarial_bdZeroPrice

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (face : ℝ) (s t : ℕ) (hs : D s ≠ 0) : bdForwardBond D face s t * D s = bdZeroPrice D face t := by
  unfold bdForwardBond bdForwardDiscount bdZeroPrice
  field_simp [hs] <;> ring
