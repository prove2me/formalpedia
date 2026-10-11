-- Prove2me | solution 1 for ActuarialValuation.crExpected_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:56:37.565322+00:00
-- url     : https://prove2.me/submissions/8285e7d8-7a52-460b-b3a1-44a6181d95a7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
open ActuarialValuation

theorem solution{n : ℕ} (p : Fin n→ℝ) : crExpected p (fun _ => 0) = 0 := by
  simp [crExpected]
