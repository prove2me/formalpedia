-- Prove2me | Definitions.Def_SourceProof_c7bae6a0333a76e8d26a8a2d
-- name    : SourceProof_c7bae6a0333a76e8d26a8a2d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:15.316697+00:00
-- url     : https://prove2.me/theorems/c42965da-e985-5a92-b191-b8a3f569f188
-- title:
--   StochLean source theorem: StochLean.exists_compact_pair_bound_of_cadlag

import Definitions.Def_SourceProof_08d1413f21e139fa3b976ce1
import Definitions.Def_SourceProof_701dc80750765cbd3c7f5808
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Compact range bounds including left limits and C1 preservation of BV -/

@[expose] public section

open Set Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_c7bae6a0333a76e8d26a8a2d {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    (T : ℝ≥0) {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2)) :
    ∃ C : ℝ, (∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Φ (x a) (x b)‖ ≤ C) ∧
      (∀ t ∈ Icc 0 T, ‖Φ (Function.leftLim x t) (x t)‖ ≤ C) := by
  obtain ⟨R, _, hR⟩ := (_root_.Prove2MeSourceProof.h_08d1413f21e139fa3b976ce1 hx) T
  have hm {t : ℝ≥0} (ht : t ∈ Icc 0 T) := _root_.Prove2MeSourceProof.h_701dc80750765cbd3c7f5808 hx hR ht
  have hK : IsCompact ((Icc (-R) R) ×ˢ (Icc (-R) R)) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := (hK.image hΦ).isBounded.exists_norm_le
  refine ⟨C, ?_, ?_⟩
  · intro a ha b hb
    exact hC _ (mem_image_of_mem (fun p : ℝ × ℝ ↦ Φ p.1 p.2)
      (show (x a, x b) ∈ (Icc (-R) R) ×ˢ (Icc (-R) R) from ⟨(hm ha).1, (hm hb).1⟩))
  · intro t ht
    exact hC _ (mem_image_of_mem (fun p : ℝ × ℝ ↦ Φ p.1 p.2)
      (show (Function.leftLim x t, x t) ∈ (Icc (-R) R) ×ˢ (Icc (-R) R) from
        ⟨(hm ht).2, (hm ht).1⟩))
end StochLean


