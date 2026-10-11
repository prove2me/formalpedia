-- Prove2me | solution 1 for ActuarialValuation.ctRateOut_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:45:33.386818+00:00
-- url     : https://prove2.me/submissions/dd118fad-7042-44c1-8afa-29d1809f969a

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctRateOut
open ActuarialValuation

theorem solution(i : Fin 3) : ctRateOut (fun _ _ => 0) i = 0 := by
  simp [ctRateOut]
