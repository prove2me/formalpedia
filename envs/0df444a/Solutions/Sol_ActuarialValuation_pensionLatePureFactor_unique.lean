-- Prove2me | solution 1 for ActuarialValuation.pensionLatePureFactor_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:12:17.390509+00:00
-- url     : https://prove2.me/submissions/2bb931c9-4d7f-4bac-a71b-78ec3f1e729a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionLatePostponedValue
import Definitions.Def_actuarial_pensionLatePureFactor
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (N D p v m A f : ℝ)
  (hden : p * v * m * A ≠ 0)
  (heq : pensionLatePostponedValue D p v m A f = N) :
  f = pensionLatePureFactor N D p v m A := by
  change f = (N - D) / (p * v * m * A)
  apply (eq_div_iff hden).2
  change D + p * v * m * A * f = N at heq
  nlinarith [heq]
