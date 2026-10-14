-- Prove2me | solution 1 for ActuarialValuation.bdZeroPrice_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:55:44.27001+00:00
-- url     : https://prove2.me/submissions/98fe997f-92a8-46b2-bc06-4d52878a2a30

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdZeroPrice

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D : ℕ → ℝ) (t : ℕ) (x y : ℝ) : bdZeroPrice D (x+y) t = bdZeroPrice D x t + bdZeroPrice D y t := by
  unfold bdZeroPrice
  ring
