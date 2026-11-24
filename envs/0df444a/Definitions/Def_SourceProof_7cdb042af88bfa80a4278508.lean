-- Prove2me | Definitions.Def_SourceProof_7cdb042af88bfa80a4278508
-- name    : SourceProof_7cdb042af88bfa80a4278508
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:42.200598+00:00
-- url     : https://prove2.me/theorems/df6989d3-8be6-4b05-9e28-54d03ebaa6ad
-- title:
--   StochLean source theorem: ProbabilityTheory.isCagladPath_step_Ioi

import Definitions.Def_StochLean_Probability_Process_Path_Caglad_F000
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Caglad initial spikes and left-open, right-closed step paths -/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_7cdb042af88bfa80a4278508 (a : ℝ≥0) (c : ℝ) :
    IsCagladPath (fun t : ℝ≥0 ↦ if a < t then c else 0) := by
  constructor
  · intro t
    change Tendsto _ (𝓝[≤] t) (𝓝 (if a < t then c else 0))
    by_cases ha : a < t
    · rw [if_pos ha]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with s hs
      exact (if_pos (show a < s from hs)).symm
    · rw [if_neg ha]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_neg (not_lt_of_ge ((show s ≤ t from hs).trans (le_of_not_gt ha)))).symm
  · intro t
    by_cases ha : a ≤ t
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (if_pos (ha.trans_lt (show t < s from hs))).symm
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ha))] with s hs
      exact (if_neg (not_lt_of_ge (show s ≤ a from (show s < a from hs).le))).symm
end ProbabilityTheory


