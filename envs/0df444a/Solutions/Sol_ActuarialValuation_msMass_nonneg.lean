-- Prove2me | solution 1 for ActuarialValuation.msMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:32:33.095978+00:00
-- url     : https://prove2.me/submissions/06a83905-98ac-4469-89bf-6a67dab644ed

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_msMass
open ActuarialValuation

theorem solution(p : Fin 3 → ℝ) (hp : ∀ i, 0 ≤ p i) : 0 ≤ msMass p := by
  unfold msMass
  exact Finset.sum_nonneg (fun i _ => hp i)
