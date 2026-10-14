-- Prove2me | solution 1 for ActuarialValuation.irCumulative_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:14:03.094906+00:00
-- url     : https://prove2.me/submissions/eeb8a90f-9ec5-4e33-a44b-a8f9da8a4f7f

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irCumulative
open ActuarialValuation

theorem solution(row : ℕ → ℝ) (n : ℕ) (h : ∀ j, 0≤row j) : 0 ≤ irCumulative row n := by
  unfold irCumulative
  exact Finset.sum_nonneg (fun j _ => h j)
