-- Prove2me | Definitions.Def_SourceProof_d1ae8a0f81c41304237a1570
-- name    : SourceProof_d1ae8a0f81c41304237a1570
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:42.377853+00:00
-- url     : https://prove2.me/theorems/4ef85ca5-c33c-55a8-825a-6cc5ec35b61a
-- title:
--   StochLean source theorem: ProbabilityTheory.StoppingTimePartition.pointNat_zero

import Definitions.Def_StochLean_Probability_Process_Partition_Sampling_F000

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

@[simp] theorem _root_.Prove2MeSourceProof.h_d1ae8a0f81c41304237a1570 (π : StoppingTimePartition F) (ω : Ω) : π.pointNat 0 ω = 0 :=
  π.first_eq_zero ω
variable {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

variable [SigmaFiniteFiltration P F]

end ProbabilityTheory.StoppingTimePartition


