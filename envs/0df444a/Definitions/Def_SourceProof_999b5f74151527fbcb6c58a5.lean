-- Prove2me | Definitions.Def_SourceProof_999b5f74151527fbcb6c58a5
-- name    : SourceProof_999b5f74151527fbcb6c58a5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:44:49.29596+00:00
-- url     : https://prove2.me/theorems/1e297685-c744-47c2-9fdd-35f9d92b861d
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_jumpProcess_of_uniformlyOn

import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_3e5346214ecefc21dfba0413
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform cadlag convergence passes to left limits and jumps

Time zero uses the source left-limit convention zero. Positive times use actual
strict-left limits; their convergence follows from uniform control, not pointwise
convergence alone.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {l : Filter ι}
  {X : ι → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_999b5f74151527fbcb6c58a5
    (hX : ∀ i, IsCadlagPath (X i · ω)) (hY : IsCadlagPath (Y · ω))
    (hu : TendstoUniformlyOn (fun i s ↦ X i s ω) (Y · ω) l (Icc 0 t)) :
    Tendsto (fun i ↦ jumpProcess (X i) t ω) l (𝓝 (jumpProcess Y t ω)) :=
  (hu.tendsto_at ⟨bot_le, le_rfl⟩).sub (_root_.Prove2MeSourceProof.h_3e5346214ecefc21dfba0413 hX hY hu)
end ProbabilityTheory


