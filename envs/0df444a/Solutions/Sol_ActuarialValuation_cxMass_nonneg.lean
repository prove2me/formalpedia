-- Prove2me | solution 1 for ActuarialValuation.cxMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:00:56.529056+00:00
-- url     : https://prove2.me/submissions/1f7af83f-9a0a-4a47-9cd8-0893d2fa9830

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxMass
open ActuarialValuation

theorem solution(f : ℕ → ℝ) (n : ℕ) (hf : ∀ j ∈ Finset.range n, 0 ≤ f j) : 0 ≤ cxMass f n := by
  unfold cxMass
  exact Finset.sum_nonneg hf
