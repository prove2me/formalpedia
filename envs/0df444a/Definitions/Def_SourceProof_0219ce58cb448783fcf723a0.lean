-- Prove2me | Definitions.Def_SourceProof_0219ce58cb448783fcf723a0
-- name    : SourceProof_0219ce58cb448783fcf723a0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:47.563693+00:00
-- url     : https://prove2.me/theorems/f037204f-510e-4a5b-9bed-83a7d0175fb7
-- title:
--   StochLean source theorem: StochLean.range_leftLim_mem_closedBall_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.Compactness.Compact

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

theorem _root_.Prove2MeSourceProof.h_0219ce58cb448783fcf723a0 (hx : IsCadlagPath x)
    {T : ℝ≥0} {R : ℝ} (hR : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ R)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) :
    x t ∈ closedBall 0 R ∧ Function.leftLim x t ∈ closedBall 0 R := by
  have hm (u : ℝ≥0) (hu : u ∈ Icc 0 T) : x u ∈ closedBall 0 R := by
    simpa only [mem_closedBall, dist_zero_right] using hR u hu
  refine ⟨hm t ht, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
    exact hm 0 ht
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht0⟩
    apply isClosed_closedBall.mem_of_tendsto (tendsto_leftLim_of_tendsto (hx.2 t ht0))
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hm u ⟨bot_le, (show u < t from hu).le.trans ht.2⟩
end StochLean


