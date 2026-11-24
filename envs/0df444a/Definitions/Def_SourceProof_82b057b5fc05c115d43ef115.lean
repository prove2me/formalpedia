-- Prove2me | Definitions.Def_SourceProof_82b057b5fc05c115d43ef115
-- name    : SourceProof_82b057b5fc05c115d43ef115
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:12:03.430673+00:00
-- url     : https://prove2.me/theorems/99abd7df-5a70-408f-b0e2-a8a8a4a60ddc
-- title:
--   StochLean source theorem: StochLean.pathTotalVariation_eq

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

theorem _root_.Prove2MeSourceProof.h_82b057b5fc05c115d43ef115 (x : ℝ≥0 → ℝ) (t : ℝ≥0) :
    pathTotalVariation x t = (eVariationOn x (Icc 0 t)).toReal := by
  change variationOnFromTo x univ 0 t = _
  rw [variationOnFromTo.eq_of_le x univ (show (0 : ℝ≥0) ≤ t from bot_le), univ_inter]
end StochLean


