-- Prove2me | Definitions.Def_SourceProof_62c96c8989b32380830efb77
-- name    : SourceProof_62c96c8989b32380830efb77
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:45.279104+00:00
-- url     : https://prove2.me/theorems/5e95fc28-85ae-4976-9267-a0504b3f92d0
-- title:
--   StochLean source theorem: StochLean.TimePartition.gap_le_mesh

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002

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

theorem _root_.Prove2MeSourceProof.h_62c96c8989b32380830efb77 (π : TimePartition T) (i : Fin π.size) : π.gap i ≤ π.mesh :=
  Finset.le_sup (f := π.gap) (Finset.mem_univ i)
end TimePartition

variable {T : ℝ≥0}

end StochLean


