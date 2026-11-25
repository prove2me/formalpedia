-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:45.0949+00:00
-- url     : https://prove2.me/theorems/515b1236-d3cc-4255-9308-aa9cba13eb88
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Refinement F000

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
import Definitions.Def_SourceProof_6eaa76d0357a33fe501c7347

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Repartitioning source simple predictable processes

The new coefficient is the old finite-step value immediately after the new left endpoint.
Its measurability is proved in that endpoint's stopping sigma-algebra. A genuine refinement
preserves the entire process and the elementary integral, including the independent time-zero
coefficient and all degenerate cells.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- Re-express coefficients on a proposed partition. Process preservation is established
below when the proposed partition actually refines the original one. -/
noncomputable def repartition (H : SimplePredictableRep F) (ρ : StoppingTimePartition F) :
    SimplePredictableRep F where
  partition := ρ
  initial := H.initial
  measurable_initial := H.measurable_initial
  coefficient := fun i ω ↦ ∑ j : Fin H.partition.size,
    if H.partition.point j.castSucc ω ≤ ρ.point i.castSucc ω ∧
        ρ.point i.castSucc ω < H.partition.point j.succ ω then H.coefficient j ω else 0
  measurable_coefficient := fun i ↦ Finset.measurable_fun_sum _ (fun j _ ↦
    (_root_.Prove2MeSourceProof.h_6eaa76d0357a33fe501c7347 (H.partition.point j.castSucc))
      (H.partition.point j.succ) (ρ.point i.castSucc) (H.measurable_coefficient j))
end ProbabilityTheory.SimplePredictableRep


