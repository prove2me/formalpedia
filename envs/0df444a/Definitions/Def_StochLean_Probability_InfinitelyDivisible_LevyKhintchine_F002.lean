-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:03.874433+00:00
-- url     : https://prove2.me/theorems/340a9958-b60a-49ce-8812-e22e541be736
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F002

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F000

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

/-- The correction forced by transporting the fixed truncation under `x ↦ a*x`. -/
noncomputable def affineDriftIntegrand (a x : ℝ) : ℝ :=
  levyTruncation (a * x) - a * levyTruncation x
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


