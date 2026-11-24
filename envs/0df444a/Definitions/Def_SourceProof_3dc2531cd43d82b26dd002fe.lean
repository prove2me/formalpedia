-- Prove2me | Definitions.Def_SourceProof_3dc2531cd43d82b26dd002fe
-- name    : SourceProof_3dc2531cd43d82b26dd002fe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:18.306329+00:00
-- url     : https://prove2.me/theorems/04f9ba8e-1534-4ccc-8363-ea5a9da26d5e
-- title:
--   StochLean source theorem: ProbabilityTheory.levyIntegrand_toReal_of_abs_lt_one

import Definitions.Def_SourceProof_c3e069bf138852082f57b309

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

theorem _root_.Prove2MeSourceProof.h_3dc2531cd43d82b26dd002fe {x : ℝ} (hx : |x| < 1) :
    (levyIntegrand x).toReal = x ^ 2 := by
  rw [_root_.Prove2MeSourceProof.h_c3e069bf138852082f57b309 hx, ENNReal.toReal_ofReal (sq_nonneg x)]
namespace IsLevyMeasure

variable {ν : Measure ℝ}

end IsLevyMeasure

end ProbabilityTheory


