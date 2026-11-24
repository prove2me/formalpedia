-- Prove2me | Definitions.Def_SourceProof_7fcabca3f7233ab3a9a0e9d6
-- name    : SourceProof_7fcabca3f7233ab3a9a0e9d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:12:01.888993+00:00
-- url     : https://prove2.me/theorems/4982bed9-3d7c-4952-9672-762f2d08a4c7
-- title:
--   StochLean source theorem: StochLean.pathTotalVariation_nonneg

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

theorem _root_.Prove2MeSourceProof.h_7fcabca3f7233ab3a9a0e9d6 (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    0 ≤ pathTotalVariation x t := variationOnFromTo.nonneg_of_le x univ bot_le
end StochLean


