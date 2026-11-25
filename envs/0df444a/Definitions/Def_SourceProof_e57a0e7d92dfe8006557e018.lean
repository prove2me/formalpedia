-- Prove2me | Definitions.Def_SourceProof_e57a0e7d92dfe8006557e018
-- name    : SourceProof_e57a0e7d92dfe8006557e018
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:39.014252+00:00
-- url     : https://prove2.me/theorems/c1dce1ba-0748-4cdc-9f14-a5fb095ff52d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.add

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5

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

theorem _root_.Prove2MeSourceProof.h_e57a0e7d92dfe8006557e018 {κ : Measure ℝ} (hν : IsLevyMeasure ν) (hκ : IsLevyMeasure κ) :
    IsLevyMeasure (ν + κ) := by
  constructor
  · simp [Measure.add_apply, (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 hν), (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 hκ)]
  · rw [lintegral_add_measure]
    exact ENNReal.add_lt_top.mpr ⟨(_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν), (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hκ)⟩
end IsLevyMeasure

end ProbabilityTheory


