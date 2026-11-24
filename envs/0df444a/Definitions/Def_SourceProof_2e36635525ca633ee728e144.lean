-- Prove2me | Definitions.Def_SourceProof_2e36635525ca633ee728e144
-- name    : SourceProof_2e36635525ca633ee728e144
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:47.364467+00:00
-- url     : https://prove2.me/theorems/5e0eb83a-e182-4bc4-924c-c77896f66254
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.smul

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


theorem _root_.Prove2MeSourceProof.h_2e36635525ca633ee728e144 (hν : IsLevyMeasure ν) (c : ℝ≥0) : IsLevyMeasure (c • ν) := by
  constructor
  · simp [Measure.smul_apply, (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 hν)]
  · rw [MeasureTheory.lintegral_smul_measure]
    exact ENNReal.mul_lt_top (by simp) (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν)
end IsLevyMeasure

end ProbabilityTheory


