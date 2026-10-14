-- Prove2me | solution 1 for ActuarialValuation.ipConvolve_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:39:06.399236+00:00
-- url     : https://prove2.me/submissions/44965369-53b9-4793-b9e9-5dde6e1fb666

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipConvolve
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (k : ℕ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) : 0≤ ipConvolve f g k := by
  unfold ipConvolve
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) (hg _))
