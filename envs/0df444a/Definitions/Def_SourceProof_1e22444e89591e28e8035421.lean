-- Prove2me | Definitions.Def_SourceProof_1e22444e89591e28e8035421
-- name    : SourceProof_1e22444e89591e28e8035421
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:52.78498+00:00
-- url     : https://prove2.me/theorems/ee5aa980-4a72-4cb2-ba2b-ae76d9ced25e
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_indicator_le

import Definitions.Def_StochLean_Probability_Process_UCP_F001

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fixed event masks preserve UCP convergence

Outer-measure comparison needs no measurability of the event or of the paths.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}
  {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_1e22444e89591e28e8035421 (s : Set Ω) (T : ℝ≥0) (ω : Ω) :
    compactDeviation (fun t ↦ s.indicator (X t)) (fun t ↦ s.indicator (Y t)) T ω ≤
      compactDeviation X Y T ω := by
  by_cases hs : ω ∈ s
  · simp only [ProbabilityTheory.compactDeviation, indicator_of_mem hs, le_refl]
  · simp only [ProbabilityTheory.compactDeviation, indicator_of_notMem hs, sub_self, norm_zero,
      ENNReal.ofReal_zero]
    exact iSup_le fun _ ↦ iSup_le fun _ ↦ bot_le
end ProbabilityTheory


