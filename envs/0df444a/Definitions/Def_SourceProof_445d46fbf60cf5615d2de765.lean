-- Prove2me | Definitions.Def_SourceProof_445d46fbf60cf5615d2de765
-- name    : SourceProof_445d46fbf60cf5615d2de765
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:19.59088+00:00
-- url     : https://prove2.me/theorems/e399dc2b-e536-4b09-9602-3f3d93fdeff1
-- title:
--   StochLean source theorem: StochLean.pVariationSum_one

import Definitions.Def_StochLean_Analysis_PathVariation_Oscillation_F000
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Comparison of variation exponents

Klenke 21.59 for continuous deterministic paths. The mesh need only tend to zero;
neither refinement nor a summable rate is imposed. Positive exponents avoid the
unintended convention that a zero increment contributes `0^0 = 1`.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology

namespace StochLean

variable {T : ℝ≥0}

@[simp] theorem _root_.Prove2MeSourceProof.h_445d46fbf60cf5615d2de765 (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    pVariationSum 1 π f = ∑ i, |π.increment f i| := by
  simp [StochLean.pVariationSum]
end StochLean


