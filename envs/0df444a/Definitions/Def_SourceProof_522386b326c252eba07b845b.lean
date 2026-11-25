-- Prove2me | Definitions.Def_SourceProof_522386b326c252eba07b845b
-- name    : SourceProof_522386b326c252eba07b845b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:46:52.125986+00:00
-- url     : https://prove2.me/theorems/db64f8c6-bdce-49ba-acbb-3fe27d667f8c
-- title:
--   StochLean source theorem: StochLean.exists_compact_vector_pair_bound_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_SourceProof_0219ce58cb448783fcf723a0
import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Mathlib.Analysis.Normed.Group.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Compact range and pair bounds for proper normed cadlag paths

The closed ball contains both each path value and its actual strict-left
limit, including the bottom endpoint's canonical Mathlib convention.
-/

@[expose] public section

open Set Filter ProbabilityTheory Metric
open scoped NNReal Topology

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

theorem _root_.Prove2MeSourceProof.h_522386b326c252eba07b845b [ProperSpace E] (hx : IsCadlagPath x)
    (T : ℝ≥0) {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2)) :
    ∃ C : ℝ, (∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Φ (x a) (x b)‖ ≤ C) ∧
      (∀ t ∈ Icc 0 T, ‖Φ (Function.leftLim x t) (x t)‖ ≤ C) := by
  obtain ⟨R, _, hR⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hx) T
  have hm {t : ℝ≥0} (ht : t ∈ Icc 0 T) := _root_.Prove2MeSourceProof.h_0219ce58cb448783fcf723a0 hx hR ht
  have hK := (isCompact_closedBall (0 : E) R).prod (isCompact_closedBall (0 : E) R)
  obtain ⟨C, hC⟩ := (hK.image hΦ).isBounded.exists_norm_le
  refine ⟨C, ?_, ?_⟩
  · intro a ha b hb
    exact hC _ (mem_image_of_mem (fun p : E × E ↦ Φ p.1 p.2)
      (show (x a, x b) ∈ closedBall (0 : E) R ×ˢ closedBall (0 : E) R from
        ⟨(hm ha).1, (hm hb).1⟩))
  · intro t ht
    exact hC _ (mem_image_of_mem (fun p : E × E ↦ Φ p.1 p.2)
      (show (Function.leftLim x t, x t) ∈ closedBall (0 : E) R ×ˢ closedBall (0 : E) R from
        ⟨(hm ht).2, (hm ht).1⟩))
end StochLean


