-- Prove2me | Definitions.Def_SourceProof_1656998222a6439ea1baa6b7
-- name    : SourceProof_1656998222a6439ea1baa6b7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:03:13.390802+00:00
-- url     : https://prove2.me/theorems/63a98cb8-3307-497f-bb08-b34e098960c6
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.quadraticTaylorErrorProcess_eq_riemann

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Partition_TaylorSums_F000
import Definitions.Def_SourceProof_1414dbb134d20c88dc05607c

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact Taylor error process on finite stopping-time partitions -/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_1656998222a6439ea1baa6b7 (π : StoppingTimePartition F)
    (f : ℝ → ℝ) (X : ℝ≥0 → Ω → ℝ) :
    π.quadraticTaylorErrorProcess f X = fun t ω ↦
      f (X (min (π.terminal ω) t) ω) - f (X 0 ω) -
        π.leftRiemannSumProcess (fun u v ↦ deriv f (X u v)) X t ω -
        (1 / 2 : ℝ) * π.weightedQuadraticCovariationSumProcess
          (fun u v ↦ deriv (deriv f) (X u v)) X X t ω := by
  funext t ω
  have h := (_root_.Prove2MeSourceProof.h_1414dbb134d20c88dc05607c (π.path ω)) f (X · ω) t
  have hs : (∑ i : Fin π.size, deriv (deriv f) (X (π.point i.castSucc ω) ω) *
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) =
      (ProbabilityTheory.StoppingTimePartition.weightedQuadraticCovariationSumProcess π)
        (fun u v ↦ deriv (deriv f) (X u v)) X X t ω := by
    unfold ProbabilityTheory.StoppingTimePartition.weightedQuadraticCovariationSumProcess
    apply sum_congr rfl
    intro i _
    ring
  change f (X (min (π.terminal ω) t) ω) - f (X 0 ω) =
    π.leftRiemannSumProcess (fun u v ↦ deriv f (X u v)) X t ω +
    (1 / 2 : ℝ) * (∑ i : Fin π.size, deriv (deriv f) (X (π.point i.castSucc ω) ω) *
      (X (min (π.point i.succ ω) t) ω - X (min (π.point i.castSucc ω) t) ω) ^ 2) +
    π.quadraticTaylorErrorProcess f X t ω at h
  rw [hs] at h
  linarith only [h]
end ProbabilityTheory.StoppingTimePartition


