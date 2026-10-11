-- Prove2me | solution 1 for ActuarialValuation.pvExpected_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:18:53.271103+00:00
-- url     : https://prove2.me/submissions/9c9497cd-6380-4a23-9ffd-e6a39bcea8e7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpected
open ActuarialValuation

theorem solution{n : ℕ} (p : Fin n → ℝ) : pvExpected p (fun _ => 0) = 0 := by
  simp [pvExpected]
