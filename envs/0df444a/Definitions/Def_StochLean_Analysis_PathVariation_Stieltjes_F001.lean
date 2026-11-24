-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_Stieltjes_F001
-- name    : StochLean_Analysis_PathVariation_Stieltjes_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:11:09.158662+00:00
-- url     : https://prove2.me/theorems/8932bc25-a906-4f17-a505-9ca22f0f2e3e
-- title:
--   StochLean: Analysis.PathVariation.Stieltjes F001

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

noncomputable def pathPositiveVariation (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (pathTotalVariation x t + x t - x 0) / 2
noncomputable def pathNegativeVariation (x : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (pathTotalVariation x t - x t + x 0) / 2
end StochLean


