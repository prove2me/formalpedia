-- Prove2me | Definitions.Def_SourceProof_59980e478d16e5d17042fad7
-- name    : SourceProof_59980e478d16e5d17042fad7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:25.574173+00:00
-- url     : https://prove2.me/theorems/5b58fcde-c7cd-4963-8f51-4bfbb7066b73
-- title:
--   StochLean source theorem: StochLean.eVariationOn_cumulativeStepSum_le

import Definitions.Def_SourceProof_0a63e289b4d83b5c6e6bf72b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Completed-cell variation sums

Completed square sums, unlike sums with a moving partial terminal cell, are
monotone in time. Their covariation analogue has total variation bounded by
the sum of the absolute increment products. This is the deterministic repair
required for Klenke 21.71, and the variation estimate behind Remark 21.61(ii).
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_59980e478d16e5d17042fad7 {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) (c : ι → ℝ) (s : Set ℝ≥0) :
    eVariationOn (cumulativeStepSum a c) s ≤ ENNReal.ofReal (∑ i, |c i|) := by
  classical
  let V := StochLean.cumulativeStepSum a (fun i ↦ |c i|)
  have hVnonneg (t : ℝ≥0) : 0 ≤ V t := by
    apply sum_nonneg
    intro i _
    split_ifs <;> simp
  have hVle (t : ℝ≥0) : V t ≤ ∑ i, |c i| := by
    apply sum_le_sum
    intro i _
    split_ifs <;> simp
  have hdist {x y : ℝ≥0} (hxy : x ≤ y) :
      dist (StochLean.cumulativeStepSum a c y) (StochLean.cumulativeStepSum a c x) ≤ V y - V x := by
    rw [Real.dist_eq, StochLean.cumulativeStepSum, StochLean.cumulativeStepSum, ← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    change (∑ i, |(if a i ≤ y then c i else 0) - (if a i ≤ x then c i else 0)|) ≤
      (∑ i, if a i ≤ y then |c i| else 0) - ∑ i, if a i ≤ x then |c i| else 0
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro i _
    by_cases hx : a i ≤ x
    · simp [hx, hx.trans hxy]
    · simp only [hx, ↓reduceIte, sub_zero]
      split_ifs <;> simp
  apply iSup_le
  rintro ⟨n, u, hu, _⟩
  simp only
  calc
    (∑ i ∈ range n, edist (StochLean.cumulativeStepSum a c (u (i + 1)))
        (StochLean.cumulativeStepSum a c (u i))) ≤
        ∑ i ∈ range n, ENNReal.ofReal (V (u (i + 1)) - V (u i)) := by
      apply sum_le_sum
      intro i _
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hdist (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (V (u n) - V (u 0)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · exact congrArg ENNReal.ofReal (sum_range_sub (fun k ↦ V (u k)) n)
      · intro i _
        exact sub_nonneg.mpr (_root_.Prove2MeSourceProof.h_0a63e289b4d83b5c6e6bf72b a (fun i ↦ abs_nonneg (c i))
          (hu (Nat.le_succ i)))
    _ ≤ ENNReal.ofReal (∑ i, |c i|) :=
      ENNReal.ofReal_le_ofReal ((sub_le_self _ (hVnonneg _)).trans (hVle _))
variable {T : ℝ≥0}

end StochLean


