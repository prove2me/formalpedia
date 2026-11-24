-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
-- name    : StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:00.153995+00:00
-- url     : https://prove2.me/theorems/865fcb8d-33fa-4849-82a0-d1e4ddc6dc7c
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyKhintchine F001

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

/-- The jump part of the real Lévy--Khintchine exponent, under the fixed strict truncation. -/
noncomputable def levyExponentIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 -
    ((t * levyTruncation x : ℝ) : ℂ) * Complex.I
/-- A simple global domination constant for the Lévy exponent integrand. -/
noncomputable def levyExponentBound (t : ℝ) : ℝ :=
  2 + (3 + |t|) * t ^ 2
namespace LevyTriplet

end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


