-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F023
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F023
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:36:30.745955+00:00
-- url     : https://prove2.me/theorems/a63c8a58-4749-4134-b733-6b20025b488b
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F023

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F021
import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F022
import Definitions.Def_SourceProof_594405e958b8c344babc33a9

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

/-- Canonical finite-jump approximation law of a general triplet. -/
noncomputable def finiteRestrictionLaw (η : LevyTriplet) (n : ℕ) : ProbabilityMeasure ℝ := by
  letI : IsFiniteMeasure (η.finiteRestriction n).jumpMeasure :=
    (_root_.Prove2MeSourceProof.h_594405e958b8c344babc33a9 η) n
  exact (η.finiteRestriction n).finiteJumpLaw
end LevyTriplet

end ProbabilityTheory


