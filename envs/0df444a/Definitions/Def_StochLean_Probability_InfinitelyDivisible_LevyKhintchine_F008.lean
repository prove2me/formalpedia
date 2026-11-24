-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F008
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:18:50.390197+00:00
-- url     : https://prove2.me/theorems/1d3fd655-6e36-4d45-a79b-7e9e67ea7c69
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F008

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001

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

noncomputable def secondDifferenceWeight (s x : ℝ) : ℝ≥0 :=
  ‖levyExponentIntegrand s x + levyExponentIntegrand (-s) x‖₊
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


