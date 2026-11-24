-- Prove2me | Definitions.Def_SourceProof_31ff967a98c1d14a8d4b3841
-- name    : SourceProof_31ff967a98c1d14a8d4b3841
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:21.989556+00:00
-- url     : https://prove2.me/theorems/312fae4a-02f0-4aeb-90f2-95dda4e8ada2
-- title:
--   StochLean source theorem: StochLean.TimePartition.leftStep_zero_fun

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-step bounds and approximation with varying horizons

Sampling uses only past values, including the initial value. Compact-uniform
approximation of a continuous function therefore needs eventual horizon coverage
and vanishing mesh, not nested partitions or a deterministic mesh rate.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

@[simp] theorem _root_.Prove2MeSourceProof.h_31ff967a98c1d14a8d4b3841 (π : TimePartition T) :
    π.leftStep (fun _ ↦ 0) = fun _ ↦ 0 := by
  funext t
  simp [StochLean.TimePartition.leftStep]
end StochLean.TimePartition


