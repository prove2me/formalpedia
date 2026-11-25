-- Prove2me | Definitions.Def_SourceProof_e0009b000942fd3d989e2e5e
-- name    : SourceProof_e0009b000942fd3d989e2e5e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:55:24.919849+00:00
-- url     : https://prove2.me/theorems/00847c34-d302-49cf-bdc0-7000c872babb
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.exists_common_partition

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_SourceProof_15e5de2b6483fa8bd27008ef
import Definitions.Def_SourceProof_96c840413a5bd52fd9e42aec

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


theorem _root_.Prove2MeSourceProof.h_e0009b000942fd3d989e2e5e (H K : SimplePredictableRep F) :
    ∃ H' K' : SimplePredictableRep F, H'.partition = K'.partition ∧
      H'.toProcess = H.toProcess ∧ K'.toProcess = K.toProcess := by
  obtain ⟨ρ, hH, hK⟩ := (_root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef H.partition) K.partition
  exact ⟨H.repartition ρ, K.repartition ρ, rfl,
    (_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec H) hH, (_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec K) hK⟩
end ProbabilityTheory.SimplePredictableRep


