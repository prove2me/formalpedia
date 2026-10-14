-- Prove2me | solution 1 for ActuarialValuation.msRowMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:04:02.919409+00:00
-- url     : https://prove2.me/submissions/a3519e68-2f4c-4fa6-a7e9-6cba7d3fb492

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msRowMass
open ActuarialValuation

theorem solution(T : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (h : ∀ j, 0 ≤ T i j) : 0 ≤ msRowMass T i := by
  unfold msRowMass
  exact Finset.sum_nonneg (fun j _ => h j)
