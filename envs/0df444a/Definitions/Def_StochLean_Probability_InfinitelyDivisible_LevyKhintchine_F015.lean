-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F015
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F015
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:20:57.432033+00:00
-- url     : https://prove2.me/theorems/93881cf8-2605-52c2-92dd-9caabeee16ba
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F015

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F005
import Definitions.Def_SourceProof_e57a0e7d92dfe8006557e018

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

/-- Addition of independent Lévy triplets. -/
noncomputable def add (η ξ : LevyTriplet) : LevyTriplet where
  gaussianVariance := η.gaussianVariance + ξ.gaussianVariance
  drift := η.drift + ξ.drift
  jumpMeasure := η.jumpMeasure + ξ.jumpMeasure
  isLevyMeasure_jumpMeasure :=
    (_root_.Prove2MeSourceProof.h_e57a0e7d92dfe8006557e018 η.isLevyMeasure_jumpMeasure) ξ.isLevyMeasure_jumpMeasure
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


