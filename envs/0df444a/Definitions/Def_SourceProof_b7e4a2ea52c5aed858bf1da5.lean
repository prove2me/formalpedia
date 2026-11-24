-- Prove2me | Definitions.Def_SourceProof_b7e4a2ea52c5aed858bf1da5
-- name    : SourceProof_b7e4a2ea52c5aed858bf1da5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:40.970256+00:00
-- url     : https://prove2.me/theorems/261ec00a-9506-4c15-9c99-2dd4164a5814
-- title:
--   StochLean source theorem: StochLean.TimePartition.taggedStep_zero

import Definitions.Def_StochLean_Analysis_PathVariation_TaggedStepApproximation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Arbitrarily tagged step approximations

Tags may be either endpoint or any point between. They need not be ordered
separately from their containing cells; repeated partition endpoints are allowed.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

@[simp] theorem _root_.Prove2MeSourceProof.h_b7e4a2ea52c5aed858bf1da5 (π : TimePartition T) (ξ : Fin π.size → ℝ≥0) (f : ℝ≥0 → ℝ) :
    π.taggedStep ξ f 0 = f 0 := by simp only [StochLean.TimePartition.taggedStep, ↓reduceIte]
end StochLean.TimePartition


