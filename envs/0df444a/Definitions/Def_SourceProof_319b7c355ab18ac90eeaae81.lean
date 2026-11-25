-- Prove2me | Definitions.Def_SourceProof_319b7c355ab18ac90eeaae81
-- name    : SourceProof_319b7c355ab18ac90eeaae81
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:10:38.742729+00:00
-- url     : https://prove2.me/theorems/3ce693b2-0b4b-5afb-93f4-c380897b5e03
-- title:
--   StochLean source theorem: ProbabilityTheory.compactDeviation_leftSampleProcess_le

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F000
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F001
import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_1f1a39edad68d4f3bc6e94ca
import Definitions.Def_SourceProof_4ffa320b02b60d0dbe7bd7da
import Definitions.Def_SourceProof_7d62dc8056c175578484d53e
import Definitions.Def_SourceProof_845eb3d5bff7aa74f6afa784
import Definitions.Def_SourceProof_8f7895612117943074291d58

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left sampling is a compact-deviation contraction

The bound is uniform over arbitrary random partitions and requires no path
regularity or measurability. It does not assert that sampling a discontinuous
path on finer partitions converges uniformly to its left-limit process.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {l : Filter ι} {X Y : ℝ≥0 → Ω → ℝ}

theorem _root_.Prove2MeSourceProof.h_319b7c355ab18ac90eeaae81 (π : StoppingTimePartition F)
    (T : ℝ≥0) (ω : Ω) :
    compactDeviation (π.leftSampleProcess X) (π.leftSampleProcess Y) T ω ≤
      compactDeviation X Y T ω := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  change ENNReal.ofReal ‖(π.path ω).leftStep (X · ω) t - (π.path ω).leftStep (Y · ω) t‖ ≤ _
  by_cases ht0 : t = 0
  · subst t
    simpa only [_root_.Prove2MeSourceProof.h_4ffa320b02b60d0dbe7bd7da] using _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 ht ω
  by_cases htπ : t ≤ π.terminal ω
  · obtain ⟨i, hi⟩ := (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π.path ω)) ⟨pos_iff_ne_zero.mpr ht0, htπ⟩
    rw [(_root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca (π.path ω)) (X · ω) hi,
      (_root_.Prove2MeSourceProof.h_1f1a39edad68d4f3bc6e94ca (π.path ω)) (Y · ω) hi]
    exact _root_.Prove2MeSourceProof.h_845eb3d5bff7aa74f6afa784 (hi.1.le.trans ht) ω
  · rw [(_root_.Prove2MeSourceProof.h_7d62dc8056c175578484d53e (π.path ω)) (X · ω) (lt_of_not_ge htπ),
      (_root_.Prove2MeSourceProof.h_7d62dc8056c175578484d53e (π.path ω)) (Y · ω) (lt_of_not_ge htπ)]
    simp only [sub_self, norm_zero, ENNReal.ofReal_zero, zero_le]
end ProbabilityTheory


