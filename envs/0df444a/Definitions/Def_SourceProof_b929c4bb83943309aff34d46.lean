-- Prove2me | Definitions.Def_SourceProof_b929c4bb83943309aff34d46
-- name    : SourceProof_b929c4bb83943309aff34d46
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:12:23.964835+00:00
-- url     : https://prove2.me/theorems/5deb5d5d-7ee7-4d45-8e68-cce71ac6922a
-- title:
--   StochLean source theorem: StochLean.rightContinuous_pathTotalVariation

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F000

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

theorem _root_.Prove2MeSourceProof.h_b929c4bb83943309aff34d46 {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ)
    (hr : ∀ t, ContinuousWithinAt x (Ici t) t) (t : ℝ≥0) :
    ContinuousWithinAt (pathTotalVariation x) (Ici t) t := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (variationOnFromTo x univ 0) (𝓝[>] t) (𝓝 (variationOnFromTo x univ 0 t))
  have h := variationOnFromTo.tendsto_right (l := x t) (mem_univ 0) (mem_univ t) hx
  simp only [univ_inter] at h
  simpa only [dist_self, add_zero] using h ((hr t).mono Ioi_subset_Ici_self)
end StochLean


