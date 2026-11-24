-- Prove2me | Definitions.Def_SourceProof_30133bca5f6836331accc046
-- name    : SourceProof_30133bca5f6836331accc046
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:53.105698+00:00
-- url     : https://prove2.me/theorems/05981b57-bb22-4184-8f60-9e6d0e84e65b
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_pos

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

theorem _root_.Prove2MeSourceProof.h_30133bca5f6836331accc046 {x : ℝ} (hx : x ≠ 0) : 0 < levyIntegrand x := by
  simp only [ProbabilityTheory.levyIntegrand, lt_min_iff, zero_lt_one, true_and]
  exact ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hx)
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


