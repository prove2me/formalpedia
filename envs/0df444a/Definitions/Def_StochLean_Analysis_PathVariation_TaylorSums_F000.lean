-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_TaylorSums_F000
-- name    : StochLean_Analysis_PathVariation_TaylorSums_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:27.582505+00:00
-- url     : https://prove2.me/theorems/de79eaae-0df4-4dd9-9b4c-70e7076b60c0
-- title:
--   StochLean: Analysis.PathVariation.TaylorSums F000

import Definitions.Def_StochLean_Analysis_PathVariation_QuadraticPairSums_F000
import Definitions.Def_StochLean_ForMathlib_Analysis_QuadraticTaylorSlope_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact second-order Taylor sums with retained partial cells -/

@[expose] public section

open Set Filter Finset
open scoped NNReal Topology

namespace StochLean

noncomputable def quadraticTaylorErrorSum {S : ℝ≥0} (π : TimePartition S)
    (f : ℝ → ℝ) (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  quadraticPairSum π (fun a b ↦ quadraticTaylorSlope f a b - deriv (deriv f) a / 2) x
end StochLean


