-- Prove2me | Definitions.Def_SourceProof_34709e9a71549d163a00e849
-- name    : SourceProof_34709e9a71549d163a00e849
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:42.32556+00:00
-- url     : https://prove2.me/theorems/c4a9b3b7-04e7-48e2-897b-83051823bc2d
-- title:
--   StochLean source theorem: StochLean.TimePartition.ceilingPoint_tendsto_nhdsGE_of_eventually_le

import Definitions.Def_StochLean_Analysis_PathVariation_Approximation_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
import Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000
import Definitions.Def_SourceProof_31206da94e8ad4f6bba4c1fa
import Definitions.Def_SourceProof_41c8e0f72444e5cb2bd104fc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Sampling a right-continuous interval step moves its endpoints upwards

Ceilings use the original partition points and are capped at its horizon.
Repeated endpoints are allowed. The increment identity is valid for every
integrator, before any right-continuity or semimartingale assumption.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_34709e9a71549d163a00e849 {U : ℕ → ℝ≥0}
    (π : (n : ℕ) → TimePartition (U n)) (a : ℝ≥0)
    (hU : ∀ᶠ n in atTop, a ≤ U n)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (π n).ceilingPoint a) atTop (𝓝[≥] a) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
      (hU.mono fun _ hn ↦ (_root_.Prove2MeSourceProof.h_31206da94e8ad4f6bba4c1fa (π _)) hn) hmesh
  · filter_upwards [hU] with n hn
    simpa only [Set.mem_Ici, min_eq_left hn] using (_root_.Prove2MeSourceProof.h_41c8e0f72444e5cb2bd104fc (π n)) a
end StochLean.TimePartition


