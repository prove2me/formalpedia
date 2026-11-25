-- Prove2me | Definitions.Def_SourceProof_adc43a2e14e55e286ae46d92
-- name    : SourceProof_adc43a2e14e55e286ae46d92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:53.220806+00:00
-- url     : https://prove2.me/theorems/68804285-d393-4704-8320-5525a1fda5df
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.measurableSet_spanningLevel

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
import Definitions.Def_SourceProof_0c6d3685872c502bae901cb3

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

theorem _root_.Prove2MeSourceProof.h_adc43a2e14e55e286ae46d92 (n : ℕ) : MeasurableSet (spanningLevel n) := by
  exact measurableSet_Ici.preimage _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3
end IsLevyMeasure

end ProbabilityTheory


