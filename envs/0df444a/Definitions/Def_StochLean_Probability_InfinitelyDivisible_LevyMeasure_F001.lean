-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
-- name    : StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:25.039141+00:00
-- url     : https://prove2.me/theorems/1b41faa6-29b3-4e85-873c-85c4f271aac1
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyMeasure F001

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

/-- Minimal real Lévy-measure semantics. -/
def IsLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ (∫⁻ x, levyIntegrand x ∂ν) < ∞
/-- A discrete infinite-activity Lévy measure with atoms geometrically approaching zero. -/
noncomputable def geometricLevyMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ ↦ Measure.dirac (((2 : ℝ)⁻¹) ^ n)
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


