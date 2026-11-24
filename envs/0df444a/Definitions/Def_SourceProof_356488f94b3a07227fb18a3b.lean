-- Prove2me | Definitions.Def_SourceProof_356488f94b3a07227fb18a3b
-- name    : SourceProof_356488f94b3a07227fb18a3b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:48:02.813913+00:00
-- url     : https://prove2.me/theorems/d11ed80a-e3bc-4c0f-ad16-9eeaa19f4d9c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.monotone_spanningLevel

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003

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

theorem _root_.Prove2MeSourceProof.h_356488f94b3a07227fb18a3b : Monotone spanningLevel := by
  intro m n hmn x hx
  exact (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hmn 1)).trans hx
end IsLevyMeasure

end ProbabilityTheory


