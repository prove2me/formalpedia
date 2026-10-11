-- Prove2me | solution 1 for ActuarialValuation.ruMean_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:27:00.474134+00:00
-- url     : https://prove2.me/submissions/1ba0d8f0-80bb-4378-8423-4036752712ed

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruMean
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) : ruMean p (fun _ => 0) = 0 := by
  simp [ruMean]
