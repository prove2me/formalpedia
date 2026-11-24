-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_Basic_F000
-- name    : StochLean_Probability_InfinitelyDivisible_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:33.901776+00:00
-- url     : https://prove2.me/theorems/4821ce70-5bac-4e23-986e-305280c8fd61
-- title:
--   StochLean: Probability.InfinitelyDivisible.Basic F000

import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F002
import Definitions.Def_StochLean_Probability_Convolution_Semigroup_F005
import Definitions.Def_SourceProof_636c524235253bfca8198f2f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Infinitely divisible probability laws

The definition is law-first: every positive convolution root must exist.  No process or path-space
realization is bundled into the predicate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory.ProbabilityMeasure

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

/-- A probability law is infinitely divisible if it has an `n`-fold convolution root for every
positive natural number `n`. -/
def IsInfinitelyDivisible (μ : ProbabilityMeasure G) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ρ : ProbabilityMeasure G, convPow ρ n = μ
end MeasureTheory.ProbabilityMeasure

namespace ProbabilityTheory

open MeasureTheory

variable {G : Type*} [AddCommMonoid G] [MeasurableSpace G] [MeasurableAdd₂ G]

end ProbabilityTheory


