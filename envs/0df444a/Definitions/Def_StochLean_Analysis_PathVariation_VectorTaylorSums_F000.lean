-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_VectorTaylorSums_F000
-- name    : StochLean_Analysis_PathVariation_VectorTaylorSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:56.950418+00:00
-- url     : https://prove2.me/theorems/48127e85-5322-46e1-8a20-00d90b757ce8
-- title:
--   StochLean: Analysis.PathVariation.VectorTaylorSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_VectorPairSums_F000
import Definitions.Def_StochLean_ForMathlib_Analysis_FrechetTaylorCoefficient_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact Frechet Taylor sums with partial terminal cells

Derivatives are sampled at the original left endpoint. After the evaluation
time, zero increments remove their contributions without moving the sample.
-/

@[expose] public section

open Set Finset
open scoped NNReal

namespace StochLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : ℝ≥0}

noncomputable def frechetTaylorErrorSum (π : TimePartition S) (f : E → ℝ)
    (x : ℝ≥0 → E) : ℝ≥0 → ℝ := normSquarePairSum π (frechetTaylorErrorCoefficient f) x
end StochLean


