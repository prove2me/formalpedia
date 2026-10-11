-- Prove2me | solution 1 for ActuarialValuation.msStep_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:13:59.999767+00:00
-- url     : https://prove2.me/submissions/4b6fe42a-9adc-4819-9f3b-83a789153497

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msStep
open ActuarialValuation

theorem solution(T : Fin 3 → Fin 3 → ℝ) (j : Fin 3) : msStep (fun _ => 0) T j = 0 := by
  simp [msStep]
