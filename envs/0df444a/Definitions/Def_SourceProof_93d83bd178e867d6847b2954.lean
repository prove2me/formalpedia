-- Prove2me | Definitions.Def_SourceProof_93d83bd178e867d6847b2954
-- name    : SourceProof_93d83bd178e867d6847b2954
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:28.293691+00:00
-- url     : https://prove2.me/theorems/f3453f9e-cf17-48ec-a0a0-1f5e1819b6ab
-- title:
--   StochLean source theorem: StochLean.variationStieltjes_measure_Ioc_sub

import Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F002
import Definitions.Def_SourceProof_dd764e40682425f1343ef671

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


theorem _root_.Prove2MeSourceProof.h_93d83bd178e867d6847b2954 (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ((positiveVariationStieltjes x hx hr).measure (Ioc s t)).toReal -
      ((negativeVariationStieltjes x hx hr).measure (Ioc s t)).toReal = x t - x s := by
  rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((StochLean.positiveVariationStieltjes x hx hr).mono hst)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((StochLean.negativeVariationStieltjes x hx hr).mono hst))]
  change (StochLean.pathPositiveVariation x t - StochLean.pathPositiveVariation x s) -
    (StochLean.pathNegativeVariation x t - StochLean.pathNegativeVariation x s) = _
  linarith [_root_.Prove2MeSourceProof.h_dd764e40682425f1343ef671 x t, _root_.Prove2MeSourceProof.h_dd764e40682425f1343ef671 x s]
end StochLean


