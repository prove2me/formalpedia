-- Prove2me | Definitions.Def_SourceProof_2ba9ae385eb9bd368051c43f
-- name    : SourceProof_2ba9ae385eb9bd368051c43f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:02:09.023082+00:00
-- url     : https://prove2.me/theorems/1081b1c4-2bc8-4644-92eb-c5b3cca9f3c0
-- title:
--   StochLean source theorem: StochLean.TimePartition.point_le_horizon

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

theorem _root_.Prove2MeSourceProof.h_2ba9ae385eb9bd368051c43f (π : TimePartition T) (i : Fin (π.size + 1)) : π.point i ≤ T := by
  exact (π.monotone_point (Fin.le_last i)).trans_eq π.last_eq_horizon
end TimePartition

variable {T : ℝ≥0}

end StochLean


