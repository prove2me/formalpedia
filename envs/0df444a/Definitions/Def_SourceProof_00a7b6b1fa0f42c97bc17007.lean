-- Prove2me | Definitions.Def_SourceProof_00a7b6b1fa0f42c97bc17007
-- name    : SourceProof_00a7b6b1fa0f42c97bc17007
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:00:59.602802+00:00
-- url     : https://prove2.me/theorems/c09f6d78-20ca-455d-988d-3d2e0c056b81
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.map_mul

import Definitions.Def_SourceProof_0c6d3685872c502bae901cb3
import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5
import Definitions.Def_SourceProof_f058d474b57c40c62282e0ea

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


theorem _root_.Prove2MeSourceProof.h_00a7b6b1fa0f42c97bc17007 (hν : IsLevyMeasure ν) {a : ℝ} (ha : a ≠ 0) :
    IsLevyMeasure (ν.map (fun x => a * x)) := by
  constructor
  · rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0)]
    have hpre : (fun x : ℝ => a * x) ⁻¹' ({0} : Set ℝ) = {0} := by
      ext x
      simp [ha]
    rw [hpre, (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 hν)]
  · rw [lintegral_map _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3 (by fun_prop)]
    refine lt_of_le_of_lt (lintegral_mono (fun x => _root_.Prove2MeSourceProof.h_f058d474b57c40c62282e0ea a x)) ?_
    rw [lintegral_const_mul _ _root_.Prove2MeSourceProof.h_0c6d3685872c502bae901cb3]
    exact ENNReal.mul_lt_top (by simp) (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν)
end IsLevyMeasure

end ProbabilityTheory


