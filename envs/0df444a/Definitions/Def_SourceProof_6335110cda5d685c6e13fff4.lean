-- Prove2me | Definitions.Def_SourceProof_6335110cda5d685c6e13fff4
-- name    : SourceProof_6335110cda5d685c6e13fff4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:25:59.802241+00:00
-- url     : https://prove2.me/theorems/8de2ed8f-2e32-5c13-82de-febc4ffc3367
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.frechetTaylorErrorProcess_eq_riemann

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_Partition_VectorTaylorSums_F000
import Definitions.Def_SourceProof_7b0f696a0d52bf7fff65ad54
import Definitions.Def_SourceProof_86753ecae2d4d5ad377d86c0
import Definitions.Def_SourceProof_9a9cf04f232727d1b4f7170b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact coordinate Taylor sums on finite stopping-time partitions

Every derivative term is an existing scalar left-Riemann or weighted mixed
sum. The partial terminal cell and all ordered coordinate pairs are retained.
-/

@[expose] public section

open MeasureTheory Finset StochLean
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
  {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_6335110cda5d685c6e13fff4 (π : StoppingTimePartition F)
    (f : (ι → ℝ) → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) :
    π.frechetTaylorErrorProcess f X = fun t ω ↦
      f (fun i ↦ X i (min (π.terminal ω) t) ω) - f (fun i ↦ X i 0 ω) -
        (∑ i, π.leftRiemannSumProcess (fun u v ↦ coordinateDeriv f i (fun j ↦ X j u v))
          (X i) t ω) -
        (1 / 2 : ℝ) * ∑ i, ∑ j, π.weightedQuadraticCovariationSumProcess
          (fun u v ↦ coordinateSecondDeriv f i j (fun k ↦ X k u v)) (X i) (X j) t ω := by
  funext t ω
  have h := (_root_.Prove2MeSourceProof.h_7b0f696a0d52bf7fff65ad54 (π.path ω)) f (fun u i ↦ X i u ω) t
  have h₁ : (∑ k : Fin π.size,
      fderiv ℝ f (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) =
      ∑ i, π.leftRiemannSumProcess (fun u v ↦ StochLean.coordinateDeriv f i (fun j ↦ X j u v))
        (X i) t ω := by
    simp_rw [_root_.Prove2MeSourceProof.h_86753ecae2d4d5ad377d86c0]
    rw [sum_comm]
    rfl
  have h₂ : (∑ k : Fin π.size,
      fderiv ℝ (fderiv ℝ f) (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) =
      ∑ i, ∑ j, π.weightedQuadraticCovariationSumProcess
        (fun u v ↦ StochLean.coordinateSecondDeriv f i j (fun k ↦ X k u v)) (X i) (X j) t ω := by
    simp_rw [_root_.Prove2MeSourceProof.h_9a9cf04f232727d1b4f7170b]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
    rfl
  change f (fun i ↦ X i (min (π.terminal ω) t) ω) - f (fun i ↦ X i 0 ω) =
    (∑ k : Fin π.size, fderiv ℝ f (fun i ↦ X i (π.point k.castSucc ω) ω)
      (fun i ↦ X i (min (π.point k.succ ω) t) ω -
        X i (min (π.point k.castSucc ω) t) ω)) +
    (1 / 2 : ℝ) * (∑ k : Fin π.size,
      fderiv ℝ (fderiv ℝ f) (fun i ↦ X i (π.point k.castSucc ω) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)
        (fun i ↦ X i (min (π.point k.succ ω) t) ω -
          X i (min (π.point k.castSucc ω) t) ω)) + π.frechetTaylorErrorProcess f X t ω at h
  rw [h₁, h₂] at h
  linarith only [h]
end ProbabilityTheory.StoppingTimePartition


