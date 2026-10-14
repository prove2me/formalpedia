-- Prove2me | solution 1 for ActuarialValuation.siSecond_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:03:16.848438+00:00
-- url     : https://prove2.me/submissions/8b82544d-8677-4257-a0bd-c65aede6783c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siSecond
open ActuarialValuation

theorem solution{m : ℕ} (p : Fin m → ℝ) (x : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) : 0 ≤ siSecond p x := by
  unfold siSecond
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hp j) (sq_nonneg _))
