-- Prove2me | Definitions.Def_SourceProof_5a9ae191ef6c23e34fa0b6ac
-- name    : SourceProof_5a9ae191ef6c23e34fa0b6ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:28.709856+00:00
-- url     : https://prove2.me/theorems/896b3f15-f651-43c7-92b8-d884defe404d
-- title:
--   StochLean source theorem: StochLean.pathPositiveVariation_add_negative

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

theorem _root_.Prove2MeSourceProof.h_5a9ae191ef6c23e34fa0b6ac (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathPositiveVariation x t + pathNegativeVariation x t = pathTotalVariation x t := by
  simp only [StochLean.pathPositiveVariation, StochLean.pathNegativeVariation]
  ring
end StochLean


