-- Prove2me | Definitions.Def_SourceProof_6a6a05e8c02fb98984eb1a4a
-- name    : SourceProof_6a6a05e8c02fb98984eb1a4a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:28:17.000383+00:00
-- url     : https://prove2.me/theorems/f46a3cbd-ed18-4da2-bfc7-163e73109501
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.coe_truncateSequence_point_le_original

import Definitions.Def_SourceProof_981f4cb9175c2d7c9fab48f7

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

theorem _root_.Prove2MeSourceProof.h_6a6a05e8c02fb98984eb1a4a (i : Fin (n + 1)) (ω : Ω) :
    ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) ≤ τ i ω := by
  rw [_root_.Prove2MeSourceProof.h_981f4cb9175c2d7c9fab48f7]
  exact min_le_right _ _
end ProbabilityTheory.StoppingTimePartition


