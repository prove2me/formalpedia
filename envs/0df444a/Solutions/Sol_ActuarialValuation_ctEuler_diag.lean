-- Prove2me | solution 1 for ActuarialValuation.ctEuler_diag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:23:39.667854+00:00
-- url     : https://prove2.me/submissions/3832697e-c8ab-41a8-ba22-e6a4917df660

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
import Definitions.Def_actuarial_ctEuler

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i : Fin 3) : ctEuler r h i i = 1-h*ctRateOut r i := by
  simp [ctEuler, ctGenerator]
  ring
