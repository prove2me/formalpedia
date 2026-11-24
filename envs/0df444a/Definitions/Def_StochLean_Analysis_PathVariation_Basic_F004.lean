-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004
-- name    : StochLean_Analysis_PathVariation_Basic_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:01:57.374343+00:00
-- url     : https://prove2.me/theorems/456d4c0f-5ee9-4bbe-9371-135b33a9ac30
-- title:
--   StochLean: Analysis.PathVariation.Basic F004

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

def increment (π : TimePartition T) (f : ℝ≥0 → ℝ) (i : Fin π.size) : ℝ :=
  f (π.right i) - f (π.left i)
end TimePartition

variable {T : ℝ≥0}

end StochLean


