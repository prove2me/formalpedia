-- Prove2me | Definitions.Def_SourceProof_45ddff72791f4617f553714f
-- name    : SourceProof_45ddff72791f4617f553714f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:20:08.079951+00:00
-- url     : https://prove2.me/theorems/8ebdd2eb-2e0a-5d8c-969a-85a82d8ed545
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_repartition

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Refinement_F000
import Definitions.Def_SourceProof_96c840413a5bd52fd9e42aec
import Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb

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

theorem _root_.Prove2MeSourceProof.h_45ddff72791f4617f553714f (H : SimplePredictableRep F) {ρ : StoppingTimePartition F}
    (hρ : ρ.Refines H.partition) (X : ℝ≥0 → Ω → ℝ) :
    (H.repartition ρ).integral X = H.integral X :=
  (_root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb (H.repartition ρ)) H ((_root_.Prove2MeSourceProof.h_96c840413a5bd52fd9e42aec H) hρ) X
end ProbabilityTheory.SimplePredictableRep


