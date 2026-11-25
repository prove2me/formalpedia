-- Prove2me | Definitions.Def_SourceProof_d36deae29721c35a59f8058d
-- name    : SourceProof_d36deae29721c35a59f8058d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:34.413613+00:00
-- url     : https://prove2.me/theorems/a6d02637-12e3-5e16-b81d-4b2c0f573dc5
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.stronglyPredictable_discreteCoefficient

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Sampling_F000
import Definitions.Def_SourceProof_97da213251d84abcdb5f1ebe

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The elementary integral as an existing discrete predictable integral

The coefficient at index `n + 1` is measurable at the original left stopping endpoint, even
when the integrator is stopped at a deterministic horizon. No deterministic bound on the
partition endpoints, or change to their sigma-fields, is imposed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal ENNReal BigOperators

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_d36deae29721c35a59f8058d (H : SimplePredictableRep F) :
    IsStronglyPredictable H.partition.sampledFiltration H.discreteCoefficient := by
  apply IsStronglyPredictable.of_measurable_add_one stronglyMeasurable_zero
  intro n
  by_cases hn : n < H.partition.size
  · simp only [ProbabilityTheory.SimplePredictableRep.discreteCoefficient, dif_pos hn]
    change StronglyMeasurable[(H.partition.pointNat n).measurableSpace]
      (H.coefficient ⟨n, hn⟩)
    have hp : H.partition.pointNat n = H.partition.point (Fin.castSucc ⟨n, hn⟩) :=
      (_root_.Prove2MeSourceProof.h_97da213251d84abcdb5f1ebe H.partition) (Fin.castSucc ⟨n, hn⟩)
    rw [hp]
    exact (H.measurable_coefficient ⟨n, hn⟩).stronglyMeasurable
  · simp only [ProbabilityTheory.SimplePredictableRep.discreteCoefficient, dif_neg hn]
    exact stronglyMeasurable_zero
end ProbabilityTheory.SimplePredictableRep


