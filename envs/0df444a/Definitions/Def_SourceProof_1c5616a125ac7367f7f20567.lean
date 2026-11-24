-- Prove2me | Definitions.Def_SourceProof_1c5616a125ac7367f7f20567
-- name    : SourceProof_1c5616a125ac7367f7f20567
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:29.683918+00:00
-- url     : https://prove2.me/theorems/6b0d2626-f64b-4100-8334-17c7b3a78f87
-- title:
--   StochLean source theorem: ProbabilityTheory.isCadlagPath_step_Ici

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right-continuous step paths at finite and infinite lifetimes

A step at zero retains its new value at zero. An infinite lifetime has no
finite-time step. No terminal process value is introduced.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [TopologicalSpace E] [Zero E]

theorem _root_.Prove2MeSourceProof.h_1c5616a125ac7367f7f20567 (a : ℝ≥0) (c : E) :
    IsCadlagPath (fun t : ℝ≥0 ↦ if a ≤ t then c else 0) := by
  constructor
  · intro t
    change Tendsto _ (𝓝[≥] t) (𝓝 (if a ≤ t then c else 0))
    by_cases ht : a ≤ t
    · rw [if_pos ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_pos (ht.trans (show t ≤ s from hs))).symm
    · rw [if_neg ht]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ht))] with s hs
      exact (if_neg (not_le_of_gt (show s < a from hs))).symm
  · intro t _
    by_cases ht : a < t
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
      exact (if_pos (show a ≤ s from (show a < s from hs).le)).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_le_of_gt ((show s < t from hs).trans_le (le_of_not_gt ht)))).symm
end ProbabilityTheory


