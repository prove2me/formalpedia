-- Prove2me | Definitions.Def_SourceProof_6f25805e568326456301e52f
-- name    : SourceProof_6f25805e568326456301e52f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:31.645803+00:00
-- url     : https://prove2.me/theorems/e5214c6c-c447-4659-af12-e3b2a11b693e
-- title:
--   StochLean source theorem: StochLean.totalVariationStieltjes_eq_add

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_5a9ae191ef6c23e34fa0b6ac

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

theorem _root_.Prove2MeSourceProof.h_6f25805e568326456301e52f (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    totalVariationStieltjes x hx hr =
      positiveVariationStieltjes x hx hr + negativeVariationStieltjes x hx hr := by
  apply StieltjesFunction.ext
  intro t
  exact (_root_.Prove2MeSourceProof.h_5a9ae191ef6c23e34fa0b6ac x t).symm
end StochLean


