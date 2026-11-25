-- Prove2me | Definitions.Def_SourceProof_29c5ae821e5120b570769687
-- name    : SourceProof_29c5ae821e5120b570769687
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:13:35.090199+00:00
-- url     : https://prove2.me/theorems/4580ba43-b6e9-4974-8c3d-652dc2deb534
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.sampledProcess_zero

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F002
import Definitions.Def_SourceProof_d1ae8a0f81c41304237a1570

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Discrete sampling on a source stopping-time partition

The finite ordered endpoint family is extended constantly after its last index. Its canonical
stopping sigma-fields and sampled process are then indexed by natural numbers, so the existing
discrete martingale and integral owners can be reused without a second finite-index calculus.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace ProbabilityTheory.StoppingTimePartition

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

@[simp] theorem _root_.Prove2MeSourceProof.h_29c5ae821e5120b570769687 {E : Type*} (π : StoppingTimePartition F)
    (X : ℝ≥0 → Ω → E) : π.sampledProcess X 0 = X 0 := by
  funext ω
  simp only [ProbabilityTheory.StoppingTimePartition.sampledProcess, _root_.Prove2MeSourceProof.h_d1ae8a0f81c41304237a1570]
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


