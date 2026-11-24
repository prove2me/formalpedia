-- Prove2me | Definitions.Def_SourceProof_6703eac8a77f9a75e40ca8b1
-- name    : SourceProof_6703eac8a77f9a75e40ca8b1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:55.734746+00:00
-- url     : https://prove2.me/theorems/ffdc3c1e-742e-4afc-866b-3cd7ecf00fa3
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.original_eq_truncateSequence_point_of_lt

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

theorem _root_.Prove2MeSourceProof.h_6703eac8a77f9a75e40ca8b1 {i : Fin (n + 1)} {ω : Ω}
    (hi : (truncateSequence τ hτ hm h0 n T).point i ω < T) :
    τ i ω = ((truncateSequence τ hτ hm h0 n T).point i ω : WithTop ℝ≥0) := by
  have hmin : min (T : WithTop ℝ≥0) (τ i ω) < (T : WithTop ℝ≥0) := by
    rw [← _root_.Prove2MeSourceProof.h_981f4cb9175c2d7c9fab48f7 τ hτ hm h0 n T i ω]
    exact WithTop.coe_lt_coe.mpr hi
  have hlt : τ i ω < (T : WithTop ℝ≥0) :=
    (min_lt_iff.mp hmin).resolve_left (lt_irrefl _)
  rw [_root_.Prove2MeSourceProof.h_981f4cb9175c2d7c9fab48f7, min_eq_right hlt.le]
end ProbabilityTheory.StoppingTimePartition


