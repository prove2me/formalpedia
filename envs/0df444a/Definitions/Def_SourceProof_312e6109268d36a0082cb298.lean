-- Prove2me | Definitions.Def_SourceProof_312e6109268d36a0082cb298
-- name    : SourceProof_312e6109268d36a0082cb298
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:05.7438+00:00
-- url     : https://prove2.me/theorems/2fbfe2d8-0799-4e1e-bb5a-d1efbab293b4
-- title:
--   StochLean source theorem: StochLean.covariationSum_mul_left

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_SourceProof_575527f7fac93af8d92ea70f

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

end TimePartition

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_312e6109268d36a0082cb298 (π : TimePartition T) (c : ℝ) (f g : ℝ≥0 → ℝ) :
    covariationSum π (fun t ↦ c * f t) g = c * covariationSum π f g := by
  simp [StochLean.covariationSum, _root_.Prove2MeSourceProof.h_575527f7fac93af8d92ea70f, mul_assoc, mul_sum]
end StochLean


