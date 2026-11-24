-- Prove2me | Definitions.Def_SourceProof_4ffa320b02b60d0dbe7bd7da
-- name    : SourceProof_4ffa320b02b60d0dbe7bd7da
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:51.187192+00:00
-- url     : https://prove2.me/theorems/14606055-a618-4624-8a6f-68344e26292c
-- title:
--   StochLean source theorem: StochLean.TimePartition.leftStep_zero

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Left-endpoint step approximation on a finite partition

Cells are left-open and right-closed. Repeated endpoints are permitted: every
positive time before the horizon belongs to exactly one nonempty cell.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace StochLean.TimePartition

variable {T : ℝ≥0}

@[simp] theorem _root_.Prove2MeSourceProof.h_4ffa320b02b60d0dbe7bd7da (π : TimePartition T) (f : ℝ≥0 → ℝ) : π.leftStep f 0 = f 0 := by
  simp only [StochLean.TimePartition.leftStep, ↓reduceIte]
end StochLean.TimePartition


