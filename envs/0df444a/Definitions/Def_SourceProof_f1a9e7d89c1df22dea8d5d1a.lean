-- Prove2me | Definitions.Def_SourceProof_f1a9e7d89c1df22dea8d5d1a
-- name    : SourceProof_f1a9e7d89c1df22dea8d5d1a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:22.940926+00:00
-- url     : https://prove2.me/theorems/92d988c6-c146-4b19-a0ac-6c8d0f1d257d
-- title:
--   StochLean source theorem: ProbabilityTheory.tendsto_step_Ioc_nhdsGT

import Definitions.Def_StochLean_Probability_Process_Path_RightLimit_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right limits of left-open, right-closed interval steps

The strict-right limit reverses the endpoint convention. The formula includes
degenerate intervals and is independent of the initial-spike convention.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_f1a9e7d89c1df22dea8d5d1a (a b t : ℝ≥0) (c : ℝ) :
    Tendsto (fun u : ℝ≥0 ↦ if a < u ∧ u ≤ b then c else 0) (𝓝[>] t)
      (𝓝 (if a ≤ t ∧ t < b then c else 0)) := by
  apply tendsto_const_nhds.congr'
  by_cases ha : a ≤ t
  · by_cases hb : t < b
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with u htu hub
      simp [ha, hb, ha.trans_lt htu, hub.le]
    · filter_upwards [self_mem_nhdsWithin] with u htu
      have hbu : b < u := (le_of_not_gt hb).trans_lt htu
      simp [hb, not_le_of_gt hbu]
  · filter_upwards [(eventually_lt_nhds (lt_of_not_ge ha)).filter_mono nhdsWithin_le_nhds]
      with u hua
    simp [ha, not_lt_of_ge hua.le]
end ProbabilityTheory


