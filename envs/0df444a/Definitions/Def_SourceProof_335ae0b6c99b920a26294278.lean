-- Prove2me | Definitions.Def_SourceProof_335ae0b6c99b920a26294278
-- name    : SourceProof_335ae0b6c99b920a26294278
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:00:39.236972+00:00
-- url     : https://prove2.me/theorems/fad46719-4d07-4eb9-a40d-69af4a56c874
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_eq_zero_of_terminal_lt

import Definitions.Def_StochLean_Analysis_PathVariation_LeftStepApproximation_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F000
import Definitions.Def_StochLean_Probability_Process_Partition_Refinement_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003

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

theorem _root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 (H : SimplePredictableRep F) {t : ℝ≥0}
    {ω : Ω} (ht : H.partition.terminal ω < t) : H.toProcess t ω = 0 := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le ht)
  rw [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg ht0]
  apply sum_eq_zero
  intro i _
  apply if_neg
  intro hi
  exact not_le_of_gt ht
    (hi.2.trans (H.partition.monotone_point ω (Fin.le_last i.succ)))
end ProbabilityTheory.SimplePredictableRep


