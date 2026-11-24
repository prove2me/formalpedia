-- Prove2me | Definitions.Def_SourceProof_153d33725319d021bbb878c0
-- name    : SourceProof_153d33725319d021bbb878c0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:56:31.209815+00:00
-- url     : https://prove2.me/theorems/4b361001-67d2-4398-9720-c23a0c6a6062
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.lintegral_lt_top

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

theorem _root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 (hν : IsLevyMeasure ν) :
    (∫⁻ x, levyIntegrand x ∂ν) < ∞ := hν.2
end IsLevyMeasure

end ProbabilityTheory


