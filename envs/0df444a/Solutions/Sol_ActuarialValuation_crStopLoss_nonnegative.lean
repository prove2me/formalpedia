-- Prove2me | solution 1 for ActuarialValuation.crStopLoss_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:03:18.714801+00:00
-- url     : https://prove2.me/submissions/55c1b1ff-50e5-4414-b7fb-99b53b405238

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crStopLoss
open ActuarialValuation

theorem solution{n : ℕ} (p X : Fin n→ℝ) (d : ℝ) (hp : ∀ i,0 ≤ p i) : 0 ≤ crStopLoss p X d := by
  unfold crStopLoss crPositivePart
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (le_max_right _ _))
