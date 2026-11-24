-- Prove2me | Definitions.Def_SourceProof_6af35797996d9e85a3ece1b8
-- name    : SourceProof_6af35797996d9e85a3ece1b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:28:25.223795+00:00
-- url     : https://prove2.me/theorems/16e0ed39-7e9e-4f0d-85a4-a29a2bec5ce0
-- title:
--   StochLean source theorem: StochLean.completedQuadraticVariationSum_mono

import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
import Definitions.Def_SourceProof_0a63e289b4d83b5c6e6bf72b

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Completed-cell variation sums

Completed square sums, unlike sums with a moving partial terminal cell, are
monotone in time. Their covariation analogue has total variation bounded by
the sum of the absolute increment products. This is the deterministic repair
required for Klenke 21.71, and the variation estimate behind Remark 21.61(ii).
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal ENNReal Topology

namespace StochLean

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_6af35797996d9e85a3ece1b8 (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    Monotone (completedQuadraticVariationSum π f) :=
  _root_.Prove2MeSourceProof.h_0a63e289b4d83b5c6e6bf72b π.right (fun _ ↦ sq_nonneg _)
end StochLean


