-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F001
-- name    : StochLean_Analysis_PathVariation_Basic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:01:38.687887+00:00
-- url     : https://prove2.me/theorems/e18fa56d-6869-4edc-8d83-931efdf993b1
-- title:
--   StochLean: Analysis.PathVariation.Basic F001

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

/-- Cell length; the ordering theorem justifies the nonnegative subtraction. -/
def gap (π : TimePartition T) (i : Fin π.size) : ℝ≥0 := π.right i - π.left i
end TimePartition

variable {T : ℝ≥0}

end StochLean


