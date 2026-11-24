-- Prove2me | Definitions.Def_SourceProof_3587e42ab751ce8dbe6b91ef
-- name    : SourceProof_3587e42ab751ce8dbe6b91ef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:48:10.516445+00:00
-- url     : https://prove2.me/theorems/f66247da-75b3-4754-ba7c-315ed803291d
-- title:
--   StochLean source theorem: StochLean.covariationSum_self

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005

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

@[simp] theorem _root_.Prove2MeSourceProof.h_3587e42ab751ce8dbe6b91ef (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    covariationSum π f f = quadraticVariationSum π f := by
  simp only [covariationSum, StochLean.quadraticVariationSum, pow_two]
end StochLean


