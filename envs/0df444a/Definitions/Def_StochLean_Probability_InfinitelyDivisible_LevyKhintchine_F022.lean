-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F022
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F022
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:22:28.021871+00:00
-- url     : https://prove2.me/theorems/a4189158-2a87-4b90-97fc-c4889d2bc017
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F022

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_86ff457032bada5981439e9c

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

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

/-- Finite-jump truncation of a general triplet along the canonical Lévy-measure exhaustion. -/
noncomputable def finiteRestriction (η : LevyTriplet) (n : ℕ) : LevyTriplet where
  gaussianVariance := η.gaussianVariance
  drift := η.drift
  jumpMeasure := η.jumpMeasure.restrict (IsLevyMeasure.spanningLevel n)
  isLevyMeasure_jumpMeasure := (_root_.Prove2MeSourceProof.h_86ff457032bada5981439e9c η.isLevyMeasure_jumpMeasure) _
end LevyTriplet

end ProbabilityTheory


