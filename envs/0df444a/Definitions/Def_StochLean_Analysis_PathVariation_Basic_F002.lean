-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
-- name    : StochLean_Analysis_PathVariation_Basic_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:15.505021+00:00
-- url     : https://prove2.me/theorems/0aabf85e-2c03-44f3-beea-dbeb97e85d6a
-- title:
--   StochLean: Analysis.PathVariation.Basic F002

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F001

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

def mesh (π : TimePartition T) : ℝ≥0 := Finset.univ.sup π.gap
end TimePartition

variable {T : ℝ≥0}

end StochLean


