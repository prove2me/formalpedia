-- Prove2me | Definitions.Def_SourceProof_afd224c326ca9c828da30ca4
-- name    : SourceProof_afd224c326ca9c828da30ca4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:50.629252+00:00
-- url     : https://prove2.me/theorems/90bee0a9-97f5-42d8-9bd0-b6c3c59d77d2
-- title:
--   StochLean source theorem: ProbabilityTheory.le_of_denseTimeUpTo_le_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Path_Supremum_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Countable running suprema and pathwise bridges

Generic process-level objects, also used by Brownian path functionals and UCP.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_afd224c326ca9c828da30ca4 {E : Type*}
    [TopologicalSpace E] [Preorder E] [OrderClosedTopology E]
    {f : ℝ≥0 → E} (hf : IsRightContinuousPath f) {T t : ℝ≥0} (ht : t ≤ T)
    {a : E} (hbound : ∀ n, f (denseTimeUpTo T n) ≤ a) : f t ≤ a := by
  have hdense : Dense (Set.range (TopologicalSpace.denseSeq ℝ≥0)) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  obtain ⟨u, _, hu, hlim⟩ := hdense.exists_seq_strictAnti_tendsto t
  have hv : Tendsto (fun n ↦ min T (u n)) atTop (𝓝 t) := by
    simpa only [min_eq_right ht] using
      ((show Tendsto (fun _ : ℕ ↦ T) atTop (𝓝 T) from tendsto_const_nhds).min hlim)
  have hwithin : Tendsto (fun n ↦ min T (u n)) atTop (nhdsWithin t (Set.Ici t)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hv, Eventually.of_forall fun n ↦ le_min ht (hu n).1.le⟩
  apply le_of_tendsto' ((hf t).tendsto.comp hwithin)
  intro n
  obtain ⟨k, hk⟩ := (hu n).2
  simpa only [ProbabilityTheory.denseTimeUpTo, hk, Function.comp_apply] using hbound k
end ProbabilityTheory


