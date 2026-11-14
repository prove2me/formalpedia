-- Prove2me | solution 1 for AFT.FiniteDist.signed_kernel_l1_contraction
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:21:35.20487+00:00
-- url     : https://prove2.me/submissions/200f1d95-1417-4b53-b9c5-1b8d949db4e6

import Definitions.Def_InfoLossLAR_Native_AFT_TotalVariation
import Mathlib



/-! Exact finite total variation and contraction by a stochastic kernel. -/

namespace AFT
end AFT
section AFT
open AFT

open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]



namespace AFT.FiniteDist
end AFT.FiniteDist
section FiniteDist
open AFT
open AFT.FiniteDist















/-- A stochastic kernel also contracts the `L¹` norm of an arbitrary signed
measure. This applies before clipping, where `TVBound.mix` alone would not. -/
theorem solution (weight : α → ℝ) (kernel : α → FiniteDist β) :
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
      ∑ input, |weight input| := by
  calc
    (∑ output, |∑ input, weight input * (kernel input).weight output|) ≤
        ∑ output, ∑ input, |weight input| * (kernel input).weight output := by
      apply Finset.sum_le_sum
      intro output _
      have h := Finset.abs_sum_le_sum_abs
        (fun input => weight input * (kernel input).weight output) Finset.univ
      simpa only [abs_mul, abs_of_nonneg ((kernel _).nonneg _)] using h
    _ = ∑ input, |weight input| := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_one, mul_one]



end FiniteDist
end AFT
