-- Prove2me | solution 1 for ActuarialValuation.siGrossSecond_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T15:53:33.239349+00:00
-- url     : https://prove2.me/submissions/27ab4e71-b40e-40d7-82df-dae0ef3afdf6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siGrossSecond
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) : 0 ≤ siGrossSecond p r := by
  unfold siGrossSecond siSecond
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (sq_nonneg _))
