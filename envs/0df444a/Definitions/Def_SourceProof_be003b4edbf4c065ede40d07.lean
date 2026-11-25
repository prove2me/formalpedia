-- Prove2me | Definitions.Def_SourceProof_be003b4edbf4c065ede40d07
-- name    : SourceProof_be003b4edbf4c065ede40d07
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:53.181909+00:00
-- url     : https://prove2.me/theorems/709b8cf2-aefa-5130-937d-66417b91f9cb
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.measure_spanningLevel_lt_top

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F001
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

theorem _root_.Prove2MeSourceProof.h_be003b4edbf4c065ede40d07 (hν : IsLevyMeasure ν) (n : ℕ) :
    ν (spanningLevel n) < ∞ := by
  let c : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hc0 : c ≠ 0 := by
    simp [c]
  have hmul : c * ν (ProbabilityTheory.IsLevyMeasure.spanningLevel n) < ∞ :=
    lt_of_le_of_lt (mul_meas_ge_le_lintegral _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3 c) hν.2
  rcases ENNReal.mul_lt_top_iff.mp hmul with h | h | h
  · exact h.2
  · exact (hc0 h).elim
  · simp [h]
end IsLevyMeasure

end ProbabilityTheory


