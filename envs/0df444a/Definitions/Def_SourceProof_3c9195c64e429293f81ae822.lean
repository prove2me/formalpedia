-- Prove2me | Definitions.Def_SourceProof_3c9195c64e429293f81ae822
-- name    : SourceProof_3c9195c64e429293f81ae822
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:26:20.645744+00:00
-- url     : https://prove2.me/theorems/1ea1baf2-2be3-427e-8f20-1c16f3f7dda0
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.coe_gaussianLaw

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F013

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

@[simp, norm_cast]
theorem _root_.Prove2MeSourceProof.h_3c9195c64e429293f81ae822 (m : ℝ) (v : ℝ≥0) :
    ((gaussianLaw m v : ProbabilityMeasure ℝ) : Measure ℝ) = gaussianReal m v := rfl
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


