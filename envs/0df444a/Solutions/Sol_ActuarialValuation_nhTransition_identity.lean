-- Prove2me | solution 1 for ActuarialValuation.nhTransition_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:17.223216+00:00
-- url     : https://prove2.me/submissions/f7adb58d-cbb0-49d0-9d02-19bc67723469

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhTransition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p t : ℝ) (i j : Fin 3) : nhTransition a b p t t i j=(if i=j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [nhTransition,nhSurvival,nhCumulative,nhExitOne,nhExitTwo]
