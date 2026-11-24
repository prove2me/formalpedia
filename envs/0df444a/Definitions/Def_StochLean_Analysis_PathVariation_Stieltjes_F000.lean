-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F000
-- name    : StochLean_Analysis_PathVariation_Stieltjes_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T15:01:54.890033+00:00
-- url     : https://prove2.me/theorems/45d879b7-fac9-42e9-bc1e-05374e43dd7c
-- title:
--   StochLean: Analysis.PathVariation.Stieltjes F000

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.LeftRight

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stieltjes components of a right-continuous locally BV path

Only Mathlib variation and Stieltjes measures are used. The components start at
zero and represent increments after time zero. The initial value is retained
separately in the reconstruction identity; it is not inserted into an unsigned
measure when it may be negative. Local BV is not mistaken for global finite mass.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

/-- Signed variation from the initial endpoint; on nonnegative time this is nonnegative. -/
noncomputable def pathTotalVariation (x : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  variationOnFromTo x univ 0
end StochLean


