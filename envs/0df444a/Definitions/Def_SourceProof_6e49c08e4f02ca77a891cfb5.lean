-- Prove2me | Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5
-- name    : SourceProof_6e49c08e4f02ca77a891cfb5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:42.940306+00:00
-- url     : https://prove2.me/theorems/927c953a-b8cf-4f35-8d5d-8e429a6bff3a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.atom_zero

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001

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

theorem _root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 (hν : IsLevyMeasure ν) : ν {0} = 0 := hν.1
end IsLevyMeasure

end ProbabilityTheory


