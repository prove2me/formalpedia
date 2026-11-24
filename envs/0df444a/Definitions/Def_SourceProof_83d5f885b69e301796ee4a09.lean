-- Prove2me | Definitions.Def_SourceProof_83d5f885b69e301796ee4a09
-- name    : SourceProof_83d5f885b69e301796ee4a09
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:38.91704+00:00
-- url     : https://prove2.me/theorems/1a3d56fe-df94-4528-b227-3842572464d8
-- title:
--   StochLean source theorem: ProbabilityTheory.isRightContinuousPath_of_locallyUniform

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
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

theorem _root_.Prove2MeSourceProof.h_83d5f885b69e301796ee4a09
    (hx : ∀ n, IsRightContinuousPath (x n))
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T)) : IsRightContinuousPath y := by
  intro t
  have hq : 𝓝[≥] t ≤ 𝓟 (Icc 0 (t + 1)) := by
    apply le_principal_iff.mpr
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one t))] with u hu
    exact ⟨bot_le, hu.le⟩
  exact ((hu (t + 1)).tendstoUniformlyOnFilter.mono_right hq).tendsto_of_eventually_tendsto
    (Eventually.of_forall fun n ↦ hx n t) ((hu (t + 1)).tendsto_at ⟨bot_le, le_add_right le_rfl⟩)
end ProbabilityTheory


