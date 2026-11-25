-- Prove2me | Definitions.Def_SourceProof_b0ba1bc04ac80bc678071fe6
-- name    : SourceProof_b0ba1bc04ac80bc678071fe6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:54.622898+00:00
-- url     : https://prove2.me/theorems/5a4b6993-26af-4eb0-a25f-eaec184e8cf7
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_eval_of_locallyUniform_of_tendsto_nhdsGE

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Evaluation of locally uniform approximations at times approaching from the right -/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_b0ba1bc04ac80bc678071fe6
    {E : Type*} [UniformSpace E] {x : ℕ → ℝ≥0 → E} {y : ℝ≥0 → E}
    (hu : ∀ T, TendstoUniformlyOn x y atTop (Icc 0 T))
    (hy : IsRightContinuousPath y) {s : ℝ≥0} {g : ℕ → ℝ≥0}
    (hg : Tendsto g atTop (𝓝[≥] s)) :
    Tendsto (fun n ↦ x n (g n)) atTop (𝓝 (y s)) := by
  have hinc : Icc s (s + 1) ⊆ Icc 0 (s + 1) :=
    fun _ ht ↦ ⟨bot_le, ht.2⟩
  apply ((hu (s + 1)).mono hinc).tendsto_comp
    ((hy s).mono (fun _ ht ↦ ht.1))
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hg.mono_right nhdsWithin_le_nhds, ?_⟩
  filter_upwards [hg.eventually self_mem_nhdsWithin,
    (hg.mono_right nhdsWithin_le_nhds).eventually_lt_const (lt_add_one s)] with n hn hlt
  exact ⟨hn, hlt.le⟩
end ProbabilityTheory


