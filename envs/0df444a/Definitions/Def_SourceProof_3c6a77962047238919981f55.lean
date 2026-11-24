-- Prove2me | Definitions.Def_SourceProof_3c6a77962047238919981f55
-- name    : SourceProof_3c6a77962047238919981f55
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:49.403969+00:00
-- url     : https://prove2.me/theorems/f3ca5c35-bace-4ced-96f0-65209bd274fb
-- title:
--   StochLean source theorem: StochLean.pathPositiveVariation_monotone

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

theorem _root_.Prove2MeSourceProof.h_3c6a77962047238919981f55 {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathPositiveVariation x) := by
  intro s t hst
  have h := variationOnFromTo.add_self_monotoneOn hx (mem_univ 0)
    (mem_univ s) (mem_univ t) hst
  change StochLean.pathTotalVariation x s + x s ≤ StochLean.pathTotalVariation x t + x t at h
  dsimp only [StochLean.pathPositiveVariation]
  linarith
end StochLean


