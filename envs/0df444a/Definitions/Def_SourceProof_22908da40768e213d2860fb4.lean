-- Prove2me | Definitions.Def_SourceProof_22908da40768e213d2860fb4
-- name    : SourceProof_22908da40768e213d2860fb4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:27.667544+00:00
-- url     : https://prove2.me/theorems/423fab43-0c0c-4771-aa81-695c432c3b61
-- title:
--   StochLean source theorem: StochLean.totalVariationStieltjes_measure_eq_add

import Definitions.Def_SourceProof_6f25805e568326456301e52f

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

theorem _root_.Prove2MeSourceProof.h_22908da40768e213d2860fb4 (x : ℝ≥0 → ℝ)
    (hx : LocallyBoundedVariationOn x univ) (hr : ∀ t, ContinuousWithinAt x (Ici t) t) :
    (totalVariationStieltjes x hx hr).measure =
      (positiveVariationStieltjes x hx hr).measure +
        (negativeVariationStieltjes x hx hr).measure := by
  rw [_root_.Prove2MeSourceProof.h_6f25805e568326456301e52f, StieltjesFunction.measure_add]
end StochLean


