-- Prove2me | solution 1 for ActuarialValuation.msRowMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:28:44.466764+00:00
-- url     : https://prove2.me/submissions/92c05726-33e4-4eb5-a295-6ba3ea9254a4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msRowMass
open ActuarialValuation

theorem solution(T : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (h : ∀ j, T i j=0) : msRowMass T i = 0 := by
  unfold msRowMass
  simp [h]
