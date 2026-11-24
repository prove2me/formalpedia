-- Prove2me | Definitions.Def_SourceProof_3e5346214ecefc21dfba0413
-- name    : SourceProof_3e5346214ecefc21dfba0413
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:20.94191+00:00
-- url     : https://prove2.me/theorems/117e2103-ca94-4a1c-99ec-759b24b211f4
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_leftLimitProcess_of_uniformlyOn

import Definitions.Def_SourceProof_12d34a5d964556d97aab2788
import Definitions.Def_SourceProof_186a2772edad25f4bcf59290
import Definitions.Def_SourceProof_3e0eeb6608a9d31d2d74e553
import Definitions.Def_SourceProof_60e710b522febb5ad2df8d23
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

theorem _root_.Prove2MeSourceProof.h_3e5346214ecefc21dfba0413
    (hX : ∀ i, IsCadlagPath (X i · ω)) (hY : IsCadlagPath (Y · ω))
    (hu : TendstoUniformlyOn (fun i s ↦ X i s ω) (Y · ω) l (Icc 0 t)) :
    Tendsto (fun i ↦ leftLimitProcess (X i) t ω) l (𝓝 (leftLimitProcess Y t ω)) := by
  by_cases ht : t = 0
  · subst t
    simpa only [_root_.Prove2MeSourceProof.h_12d34a5d964556d97aab2788, Pi.zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  · let : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hq : 𝓝[<] t ≤ 𝓟 (Icc 0 t) := by
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ⟨bot_le, hs.le⟩
    exact (_root_.Prove2MeSourceProof.h_3e0eeb6608a9d31d2d74e553 hu) hq (fun i ↦ (_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 (hX i)) ht)
      ((_root_.Prove2MeSourceProof.h_186a2772edad25f4bcf59290 hY) ht)
end ProbabilityTheory


