-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F001
-- name    : StochLean_Analysis_PathVariation_CompletedSums_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:20.50783+00:00
-- url     : https://prove2.me/theorems/5013601c-fd66-40f7-94a9-f285ed22cd3a
-- title:
--   StochLean: Analysis.PathVariation.CompletedSums F001

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F004
import Definitions.Def_StochLean_Analysis_PathVariation_CompletedSums_F000

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

noncomputable def completedQuadraticVariationSum (π : TimePartition T)
    (f : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  cumulativeStepSum π.right (fun i ↦ (π.increment f i) ^ 2)
noncomputable def completedCovariationSum (π : TimePartition T)
    (f g : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  cumulativeStepSum π.right (fun i ↦ π.increment f i * π.increment g i)
end StochLean


