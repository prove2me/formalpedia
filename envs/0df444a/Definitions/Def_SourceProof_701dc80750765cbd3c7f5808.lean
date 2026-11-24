-- Prove2me | Definitions.Def_SourceProof_701dc80750765cbd3c7f5808
-- name    : SourceProof_701dc80750765cbd3c7f5808
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:07.434131+00:00
-- url     : https://prove2.me/theorems/c8dc12f2-6528-4028-8c88-c8d67c685a48
-- title:
--   StochLean source theorem: StochLean.range_leftLim_mem_Icc_of_cadlag

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Compactness.Compact
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

theorem _root_.Prove2MeSourceProof.h_701dc80750765cbd3c7f5808 {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {T : ℝ≥0} {R : ℝ} (hR : ∀ t ∈ Icc 0 T, ‖x t‖ ≤ R)
    {t : ℝ≥0} (ht : t ∈ Icc 0 T) :
    x t ∈ Icc (-R) R ∧ Function.leftLim x t ∈ Icc (-R) R := by
  have hm (u : ℝ≥0) (hu : u ∈ Icc 0 T) : x u ∈ Icc (-R) R := by
    simpa only [Real.norm_eq_abs, abs_le, mem_Icc] using hR u hu
  refine ⟨hm t ht, ?_⟩
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ ↦ bot_le)]
    exact hm 0 ht
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht0
    let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    apply isClosed_Icc.mem_of_tendsto (tendsto_leftLim_of_tendsto (hx.2 t ht0))
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hm u ⟨bot_le, (show u < t from hu).le.trans ht.2⟩
end StochLean


