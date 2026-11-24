-- Prove2me | Definitions.Def_SourceProof_575527f7fac93af8d92ea70f
-- name    : SourceProof_575527f7fac93af8d92ea70f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:13.9118+00:00
-- url     : https://prove2.me/theorems/59f46e8c-a28c-4da4-b519-efaeda03d23f
-- title:
--   StochLean source theorem: StochLean.TimePartition.increment_mul

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004

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

theorem _root_.Prove2MeSourceProof.h_575527f7fac93af8d92ea70f (π : TimePartition T) (c : ℝ) (f : ℝ≥0 → ℝ) (i : Fin π.size) :
    π.increment (fun t ↦ c * f t) i = c * π.increment f i := by
  simp only [StochLean.TimePartition.increment]
  ring
end TimePartition

variable {T : ℝ≥0}

end StochLean


