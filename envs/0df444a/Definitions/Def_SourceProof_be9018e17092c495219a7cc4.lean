-- Prove2me | Definitions.Def_SourceProof_be9018e17092c495219a7cc4
-- name    : SourceProof_be9018e17092c495219a7cc4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:20.968489+00:00
-- url     : https://prove2.me/theorems/f50af964-54aa-41df-b19e-576c42cf54b6
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_toReal_of_one_le_abs

import Definitions.Def_SourceProof_61527dde036c91b88ebdd404

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

theorem _root_.Prove2MeSourceProof.h_be9018e17092c495219a7cc4 {x : ℝ} (hx : 1 ≤ |x|) :
    (levyIntegrand x).toReal = 1 := by
  rw [_root_.Prove2MeSourceProof.h_61527dde036c91b88ebdd404 hx]
  simp
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


