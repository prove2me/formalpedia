-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F007
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:30:00.778932+00:00
-- url     : https://prove2.me/theorems/ad2f98c5-9298-4a27-ab6a-e7e8e7cbd5e1
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F007

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F006

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

/-- A triplet represents a real probability law when the characteristic function is the
exponential of its fixed-truncation exponent. -/
def Represents (η : LevyTriplet) (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ t, charFun (μ : Measure ℝ) t = Complex.exp (η.exponent t)
/-- Existence and uniqueness of a representing triplet, separated from the triplet data itself. -/
def HasUniqueLevyTriplet (μ : ProbabilityMeasure ℝ) : Prop :=
  ∃! η : LevyTriplet, η.Represents μ
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


