-- Prove2me | Definitions.Def_SourceProof_1b364b3ac1881eb32ea6aaf9
-- name    : SourceProof_1b364b3ac1881eb32ea6aaf9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:43.23087+00:00
-- url     : https://prove2.me/theorems/7d79c4a7-6db2-49cb-9a50-2b0bc3cbe873
-- title:
--   StochLean source theorem: StochLean.pathNegativeVariation_monotone

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

theorem _root_.Prove2MeSourceProof.h_1b364b3ac1881eb32ea6aaf9 {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathNegativeVariation x) := by
  intro s t hst
  have h := variationOnFromTo.sub_self_monotoneOn hx (mem_univ 0)
    (mem_univ s) (mem_univ t) hst
  change StochLean.pathTotalVariation x s - x s ≤ StochLean.pathTotalVariation x t - x t at h
  dsimp only [StochLean.pathNegativeVariation]
  linarith
end StochLean


