-- Prove2me | Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F000
-- name    : StochLean_Probability_InfinitelyDivisible_LevyMeasure_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:43.499051+00:00
-- url     : https://prove2.me/theorems/920ba774-d32e-46bf-b463-edb41c79d5ef
-- title:
--   StochLean: Probability.InfinitelyDivisible.LevyMeasure F000

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

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

/-- The canonical nonnegative Lévy integrand `min(1,x²)`. -/
noncomputable def levyIntegrand (x : ℝ) : ℝ≥0∞ :=
  min 1 (ENNReal.ofReal (x ^ 2))
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


