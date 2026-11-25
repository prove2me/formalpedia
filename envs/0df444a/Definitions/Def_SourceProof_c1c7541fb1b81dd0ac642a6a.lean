-- Prove2me | Definitions.Def_SourceProof_c1c7541fb1b81dd0ac642a6a
-- name    : SourceProof_c1c7541fb1b81dd0ac642a6a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:40.285231+00:00
-- url     : https://prove2.me/theorems/a6fccc19-c385-48c5-a40b-c377a8086af7
-- title:
--   StochLean source theorem: ProbabilityTheory.isCadlagPath_of_locallyUniform

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_SourceProof_78da39830a86073c1a81eb5d
import Definitions.Def_SourceProof_83d5f885b69e301796ee4a09
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Locally uniform limits of cadlag paths

The finite left limit is constructed using completeness of the state space.
No convergence of the left limits is postulated, and time zero needs no left limit.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [MetricSpace E] {x : ℕ → ℝ≥0 → E} {y : ℝ≥0 → E}

theorem _root_.Prove2MeSourceProof.h_c1c7541fb1b81dd0ac642a6a [CompleteSpace E]
    (hx : ∀ n, IsCadlagPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T)) : IsCadlagPath y := by
  refine ⟨_root_.Prove2MeSourceProof.h_83d5f885b69e301796ee4a09 (fun n ↦ (hx n).1) hu, ?_⟩
  intro t ht
  let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
  have hq : 𝓝[<] t ≤ 𝓟 (Icc 0 t) := by
    apply le_principal_iff.mpr
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact ⟨bot_le, hu.le⟩
  exact (_root_.Prove2MeSourceProof.h_78da39830a86073c1a81eb5d (hu t)) hq (fun n ↦ (hx n).2 t ht)
end ProbabilityTheory


