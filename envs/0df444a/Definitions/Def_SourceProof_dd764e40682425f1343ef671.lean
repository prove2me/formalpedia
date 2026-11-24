-- Prove2me | Definitions.Def_SourceProof_dd764e40682425f1343ef671
-- name    : SourceProof_dd764e40682425f1343ef671
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:23.767858+00:00
-- url     : https://prove2.me/theorems/57b00f80-0fd3-4e3f-b6b8-50c48f23e3eb
-- title:
--   StochLean source theorem: StochLean.pathPositiveVariation_sub_negative

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F001

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

theorem _root_.Prove2MeSourceProof.h_dd764e40682425f1343ef671 (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathPositiveVariation x t - pathNegativeVariation x t = x t - x 0 := by
  simp only [StochLean.pathPositiveVariation, StochLean.pathNegativeVariation]
  ring
end StochLean


