-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
-- name    : StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:20.878144+00:00
-- url     : https://prove2.me/theorems/32d72222-a512-43c8-a773-de5dda72f6c2
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyMeasure F003

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy measures on the real line

The primitive predicate contains exactly the zero-atom condition and finiteness of the truncated
second moment.  Sigma-finiteness is derived by a countable level-set exhaustion and is deliberately
not installed as a global instance.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace IsLevyMeasure

variable {ν : Measure ℝ}

/-- Positive level sets of the Lévy integrand.
Their thresholds are strictly positive and finite. -/
def spanningLevel (n : ℕ) : Set ℝ :=
  {x | ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ levyIntegrand x}
end IsLevyMeasure

end ProbabilityTheory


