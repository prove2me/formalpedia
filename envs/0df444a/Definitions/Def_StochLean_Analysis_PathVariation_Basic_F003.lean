-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
-- name    : StochLean_Analysis_PathVariation_Basic_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:01:50.421976+00:00
-- url     : https://prove2.me/theorems/b5c9ac6d-a109-4c66-814a-6f29dc73f32a
-- title:
--   StochLean: Analysis.PathVariation.Basic F003

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

def empty : TimePartition 0 where
  size := 0
  point := fun _ ↦ 0
  monotone_point := monotone_const
  first_eq_zero := rfl
  last_eq_horizon := rfl
def single (T : ℝ≥0) : TimePartition T where
  size := 1
  point := ![0, T]
  monotone_point := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first_eq_zero := rfl
  last_eq_horizon := rfl
end TimePartition

variable {T : ℝ≥0}

end StochLean


