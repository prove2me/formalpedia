-- Prove2me | solution 1 for ActuarialValuation.utExpected_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:52:08.481042+00:00
-- url     : https://prove2.me/submissions/f44f9ccc-fef3-4952-9c16-fc09d74febf8

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utExpected
open ActuarialValuation

theorem solution{n : ℕ} (p : Fin n → ℝ) : utExpected p (fun _ => 0)=0 := by
  simp [utExpected]
