-- Prove2me | Definitions.Def_SourceProof_0c6d3685872c502bae901cb3
-- name    : SourceProof_0c6d3685872c502bae901cb3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:20.666429+00:00
-- url     : https://prove2.me/theorems/1516ea18-fd42-4183-b209-f1bf465aea5b
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_levyIntegrand

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

theorem _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3 : Measurable levyIntegrand := by
  exact measurable_const.min
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2))
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


