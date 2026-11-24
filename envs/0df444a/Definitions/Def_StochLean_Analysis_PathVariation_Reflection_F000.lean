-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Reflection_F000
-- name    : StochLean_Analysis_PathVariation_Reflection_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:16.182246+00:00
-- url     : https://prove2.me/theorems/88e74a94-0edd-46ab-855d-d943142731aa
-- title:
--   StochLean: Analysis.PathVariation.Reflection F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reflection of deterministic paths and invariance of square sums

There is no probability space in this layer. Flipping all increments of one interval preserves
every square sum whose partition contains both endpoints, including repeated endpoints.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

def reflectAfterPath (f : ℝ≥0 → ℝ) (a : ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ 2 * f (min t a) - f t
def flipIntervalPath (f : ℝ≥0 → ℝ) (a b : ℝ≥0) : ℝ≥0 → ℝ :=
  fun t ↦ f t - 2 * (f (min t b) - f (min t a))
end StochLean


