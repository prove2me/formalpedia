-- Prove2me | Definitions.Def_SourceProof_981f4cb9175c2d7c9fab48f7
-- name    : SourceProof_981f4cb9175c2d7c9fab48f7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:26.12681+00:00
-- url     : https://prove2.me/theorems/3f472fc1-a473-4bf4-858b-4dad6b393b13
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.coe_truncateSequence_point

import Definitions.Def_StochLean_Probability_Process_Partition_TruncateSequence_F000
import Definitions.Def_SourceProof_713ea2978da3b3a620edf296

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite capped partitions of an increasing stopping sequence

All `n` cells, including the first one, are retained. Stopping times may be infinite;
the finite cap gives everywhere-finite endpoints and repeated capped endpoints are legal.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

variable (τ : ℕ → Ω → WithTop ℝ≥0) (hτ : ∀ n, IsStoppingTime F (τ n))
  (hm : ∀ ω, Monotone (τ · ω)) (h0 : ∀ ω, τ 0 ω = 0) (n : ℕ) (T : ℝ≥0)

@[simp] theorem _root_.Prove2MeSourceProof.h_981f4cb9175c2d7c9fab48f7 (i : Fin (n + 1)) (ω : Ω) :
    ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) =
      min (T : WithTop ℝ≥0) (τ i ω) :=
  congrFun (_root_.Prove2MeSourceProof.h_713ea2978da3b3a620edf296 (hτ i) T) ω
end ProbabilityTheory.StoppingTimePartition


