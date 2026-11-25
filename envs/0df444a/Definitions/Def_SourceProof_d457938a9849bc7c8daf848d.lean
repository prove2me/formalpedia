-- Prove2me | Definitions.Def_SourceProof_d457938a9849bc7c8daf848d
-- name    : SourceProof_d457938a9849bc7c8daf848d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:56.657748+00:00
-- url     : https://prove2.me/theorems/3d6d41e4-2570-535d-ac04-5a5fc59f159c
-- title:
--   StochLean source theorem: StochLean.quadraticVariationSum_stop_eq_completed_of_mem_point

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_SourceProof_100a4fbbee9cf0e8517b3b4d
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Order
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Monotone endpoint-projected square sums

Partial-cell square sums need not increase in time. At partition endpoints
they equal completed-cell sums; composing with the monotone upper endpoint
projection therefore gives genuinely increasing approximants, even for jumps.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_d457938a9849bc7c8daf848d
    (π : TimePartition T) (f : ℝ≥0 → ℝ) {s : ℝ≥0} (hs : s ∈ Set.range π.point) :
    quadraticVariationSum π (fun t ↦ f (min t s)) = completedQuadraticVariationSum π f s := by
  classical
  unfold StochLean.quadraticVariationSum StochLean.completedQuadraticVariationSum StochLean.cumulativeStepSum
  apply Finset.sum_congr rfl
  intro i _
  rcases (_root_.Prove2MeSourceProof.h_100a4fbbee9cf0e8517b3b4d π) hs i with h | h
  · by_cases hr : π.right i ≤ s
    · have hle : π.left i ≤ s := ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i).trans hr
      simp only [StochLean.TimePartition.increment, if_pos hr, min_eq_left hr, min_eq_left hle]
    · have hsr : s ≤ π.right i := h.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i)
      simp only [StochLean.TimePartition.increment, if_neg hr, min_eq_right h, min_eq_right hsr,
        sub_self, zero_pow (by norm_num : 2 ≠ 0)]
  · have hl := ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 π) i).trans h
    simp only [StochLean.TimePartition.increment, if_pos h, min_eq_left h, min_eq_left hl]
end StochLean


