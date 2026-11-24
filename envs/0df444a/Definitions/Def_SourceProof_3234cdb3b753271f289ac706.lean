-- Prove2me | Definitions.Def_SourceProof_3234cdb3b753271f289ac706
-- name    : SourceProof_3234cdb3b753271f289ac706
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:12.385536+00:00
-- url     : https://prove2.me/theorems/4466385f-07cd-4305-a548-c41ebdfa5175
-- title:
--   StochLean source theorem: StochLean.totalVariationStieltjes_measure_Ioc

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002

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


theorem _root_.Prove2MeSourceProof.h_3234cdb3b753271f289ac706 (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (totalVariationStieltjes x hx hr).measure (Ioc s t) = eVariationOn x (Icc s t) := by
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (variationOnFromTo x univ 0 t - variationOnFromTo x univ 0 s) = _
  rw [variationOnFromTo.sub_right hx (mem_univ 0) (mem_univ t) (mem_univ s),
    variationOnFromTo.eq_of_le x univ hst, univ_inter]
  apply ENNReal.ofReal_toReal
  simpa only [BoundedVariationOn, univ_inter] using hx s t (mem_univ s) (mem_univ t)
end StochLean


