-- Prove2me | Definitions.Def_SourceProof_6132ae08b0208d84e9cba7c3
-- name    : SourceProof_6132ae08b0208d84e9cba7c3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:27:23.011374+00:00
-- url     : https://prove2.me/theorems/a7452c23-8932-4b28-a8c9-0f600d1a0093
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_zero

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_6132ae08b0208d84e9cba7c3 : levyIntegrand 0 = 0 := by
  simp [ProbabilityTheory.levyIntegrand]
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


