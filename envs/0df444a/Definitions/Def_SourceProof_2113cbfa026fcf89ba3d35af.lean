-- Prove2me | Definitions.Def_SourceProof_2113cbfa026fcf89ba3d35af
-- name    : SourceProof_2113cbfa026fcf89ba3d35af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:07.101867+00:00
-- url     : https://prove2.me/theorems/48f1160d-cdaa-4db4-881e-4b156257196b
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_eq_initial_add_discreteStochasticIntegral

import Definitions.Def_StochLean_Probability_Martingale_DiscreteIntegral_F000
import Definitions.Def_SourceProof_8db4335308fcb07f2558487f
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

theorem _root_.Prove2MeSourceProof.h_2113cbfa026fcf89ba3d35af (H : SimplePredictableRep F)
    (X : ℝ≥0 → Ω → ℝ) :
    H.integral X = fun ω ↦ H.initial ω * X 0 ω +
      discreteStochasticIntegral H.discreteCoefficient (H.partition.sampledProcess X)
        H.partition.size ω := by
  funext ω
  rw [ProbabilityTheory.SimplePredictableRep.integral, MeasureTheory.discreteStochasticIntegral, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [(_root_.Prove2MeSourceProof.h_8db4335308fcb07f2558487f H) i]
  have hl : H.partition.pointNat i = H.partition.point i.castSucc :=
    (_root_.Prove2MeSourceProof.h_97da213251d84abcdb5f1ebe H.partition) i.castSucc
  have hr : H.partition.pointNat (i + 1) = H.partition.point i.succ :=
    (_root_.Prove2MeSourceProof.h_97da213251d84abcdb5f1ebe H.partition) i.succ
  simp only [ProbabilityTheory.StoppingTimePartition.sampledProcess, hl, hr, smul_eq_mul]
end ProbabilityTheory.SimplePredictableRep


