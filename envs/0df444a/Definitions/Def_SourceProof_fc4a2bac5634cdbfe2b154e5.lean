-- Prove2me | Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
-- name    : SourceProof_fc4a2bac5634cdbfe2b154e5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:02:07.512268+00:00
-- url     : https://prove2.me/theorems/9b79db56-016b-4ede-961c-79dd073b6afd
-- title:
--   StochLean source theorem: StochLean.TimePartition.left_le_right

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Deterministic variation along finite partitions

This layer has no probability space or filtration. Partitions may repeat endpoints;
zero-length cells contribute zero to quadratic variation. The empty partition is
available precisely at horizon zero. Raw stochastic brackets, which retain the
initial square, are not defined here.
-/

@[expose] public section

open Filter Finset
open scoped NNReal Topology BigOperators

namespace StochLean

namespace TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (π : TimePartition T) (i : Fin π.size) : π.left i ≤ π.right i :=
  π.monotone_point (by simp [Fin.le_def])
end TimePartition

variable {T : ℝ≥0}

end StochLean


