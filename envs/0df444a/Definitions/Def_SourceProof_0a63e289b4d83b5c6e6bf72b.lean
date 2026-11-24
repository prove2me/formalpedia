-- Prove2me | Definitions.Def_SourceProof_0a63e289b4d83b5c6e6bf72b
-- name    : SourceProof_0a63e289b4d83b5c6e6bf72b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:10:25.582842+00:00
-- url     : https://prove2.me/theorems/20120f49-beb2-4d94-bbde-8c68def2f068
-- title:
--   StochLean source theorem: StochLean.cumulativeStepSum_mono

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F000

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

theorem _root_.Prove2MeSourceProof.h_0a63e289b4d83b5c6e6bf72b {ι : Type*} [Fintype ι]
    (a : ι → ℝ≥0) {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) :
    Monotone (cumulativeStepSum a c) := by
  intro s t hst
  apply sum_le_sum
  intro i _
  by_cases hs : a i ≤ s
  · simp [hs, hs.trans hst]
  · simp only [hs, ↓reduceIte]
    split_ifs <;> simp [hc]
variable {T : ℝ≥0}

end StochLean


