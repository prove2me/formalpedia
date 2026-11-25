-- Prove2me | Definitions.Def_SourceProof_f10c0f6fee878e1d0d16f7ba
-- name    : SourceProof_f10c0f6fee878e1d0d16f7ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:52:59.227933+00:00
-- url     : https://prove2.me/theorems/8a40d0d2-e9ed-44a2-9966-69ae1f6ed28c
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.weightedQuadraticCovariationSumProcess_eq_riemann

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Partition_WeightedCrossSums_F000
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual weighted mixed increment sums

Weights are sampled at the original left endpoints. The moving partial cell
is retained, and zero-length cells are allowed. These increment sums have no
initial atom, unlike the raw mixed bracket itself.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_f10c0f6fee878e1d0d16f7ba (π : StoppingTimePartition F)
    (H X Y : ℝ≥0 → Ω → ℝ) :
    π.weightedQuadraticCovariationSumProcess H X Y =
      π.leftRiemannSumProcess H (X * Y) - π.leftRiemannSumProcess (H * X) Y -
        π.leftRiemannSumProcess (H * Y) X := by
  funext t ω
  simp only [ProbabilityTheory.StoppingTimePartition.weightedQuadraticCovariationSumProcess, ProbabilityTheory.StoppingTimePartition.leftRiemannSumProcess,
    Pi.sub_apply, Pi.mul_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : π.point i.castSucc ω ≤ t
  · rw [min_eq_left hi]
    ring
  · have ht : t ≤ π.point i.castSucc ω := (lt_of_not_ge hi).le
    have htr : t ≤ π.point i.succ ω := ht.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π.path ω)) i)
    simp only [min_eq_right ht, min_eq_right htr, sub_self, mul_zero]
end ProbabilityTheory.StoppingTimePartition


