-- Prove2me | Definitions.Def_SourceProof_7d2787f4ad27ed704ba3ff83
-- name    : SourceProof_7d2787f4ad27ed704ba3ff83
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:11:43.072244+00:00
-- url     : https://prove2.me/theorems/c018230a-786b-4802-979e-2b164d41fcb6
-- title:
--   StochLean source theorem: StochLean.pathTotalVariation_monotone

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

theorem _root_.Prove2MeSourceProof.h_7d2787f4ad27ed704ba3ff83 {x : ℝ≥0 → ℝ}
    (hx : LocallyBoundedVariationOn x univ) : Monotone (pathTotalVariation x) :=
  fun _ _ hst ↦ variationOnFromTo.monotoneOn hx (mem_univ 0) (mem_univ _) (mem_univ _) hst
end StochLean


