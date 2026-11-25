-- Prove2me | Definitions.Def_SourceProof_8fd5626f1050c626fa529bb3
-- name    : SourceProof_8fd5626f1050c626fa529bb3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:54.685295+00:00
-- url     : https://prove2.me/theorems/0cf1cc59-14f0-43a3-acf4-4ba9f62df49f
-- title:
--   StochLean source theorem: StochLean.locallyBoundedVariationOn_tsum_monotone_indicator

import Definitions.Def_SourceProof_798d59aac4a0874192da8eb2
import Definitions.Def_SourceProof_93f0177984c2fc01cc45a1ac
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Variation of absolutely summable coefficients with nested cutoffs

An increasing family of index sets may activate each signed coefficient
at most once. Splitting its positive and negative parts gives the actual
sum as a difference of two monotone functions, without enumerating the
index type or imposing a sign on the coefficients.
-/

@[expose] public section

open Set

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8fd5626f1050c626fa529bb3
    {α ι : Type*} [LinearOrder α] {a : α → Set ι} (ha : Monotone a)
    {w : ι → ℝ} (hw : Summable (fun i ↦ |w i|)) :
    LocallyBoundedVariationOn (fun t ↦ ∑' i, (a t).indicator w i) univ := by
  classical
  let p : ι → ℝ := fun i ↦ (|w i| + w i) / 2
  let n : ι → ℝ := fun i ↦ (|w i| - w i) / 2
  have hp : Summable p := (hw.add hw.of_abs).div_const 2
  have hn : Summable n := (hw.sub hw.of_abs).div_const 2
  have hp0 (i : ι) : 0 ≤ p i := by
    have h := neg_abs_le (w i)
    dsimp only [p]
    linarith only [h]
  have hn0 (i : ι) : 0 ≤ n i := by
    have h := le_abs_self (w i)
    dsimp only [n]
    linarith only [h]
  have hpm := _root_.Prove2MeSourceProof.h_93f0177984c2fc01cc45a1ac ha hp hp0
  have hnm := _root_.Prove2MeSourceProof.h_93f0177984c2fc01cc45a1ac ha hn hn0
  have hv := _root_.Prove2MeSourceProof.h_798d59aac4a0874192da8eb2 (hpm.monotoneOn univ).locallyBoundedVariationOn
    (hnm.monotoneOn univ).locallyBoundedVariationOn
  have he : (fun t ↦ (∑' i, (a t).indicator p i) - ∑' i, (a t).indicator n i) =
      fun t ↦ ∑' i, (a t).indicator w i := by
    funext t
    rw [← (hp.indicator (a t)).tsum_sub (hn.indicator (a t))]
    apply tsum_congr
    intro i
    by_cases hi : i ∈ a t
    · simp only [indicator_of_mem hi, p, n]
      ring
    · simp only [indicator_of_notMem hi, sub_zero]
  rwa [he] at hv
end StochLean


