-- Prove2me | solution 1 for ActuarialValuation.ruExponential_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:38:08.558148+00:00
-- url     : https://prove2.me/submissions/9e5c3b9c-6fdb-4fb2-a9e5-84f65b4b24d2

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruExponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (R x y : ℝ) :
    ruExponential R (x+y) = ruExponential R x * ruExponential R y := by
  unfold ruExponential
  rw [mul_add, Real.exp_add]
