-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:40.659042+00:00
-- url     : https://prove2.me/theorems/2aabc0da-d0ae-4eb7-8987-2679abb476e5
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Normalization F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
import Definitions.Def_SourceProof_73741c513a21a80e8e3a86fa

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Removing irrelevant coefficients on zero-length stopping intervals

A bounded simple process can have unbounded representation coefficients on empty intervals.
Set those coefficients to zero before using a coefficient-wise martingale estimate. The process
and its elementary integral are unchanged, and measurability is retained at the left endpoint.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped NNReal

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- Normalize only coefficients on empty intervals; the source permits these unbounded
coefficients, so bounding them must be a proved reduction, not an added assumption. -/
noncomputable def removeEmptyIntervals (H : SimplePredictableRep F) : SimplePredictableRep F where
  partition := H.partition
  initial := H.initial
  measurable_initial := H.measurable_initial
  coefficient := fun i ↦
    {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω}.indicator (H.coefficient i)
  measurable_coefficient := fun i ↦
    (H.measurable_coefficient i).indicator ((_root_.Prove2MeSourceProof.h_73741c513a21a80e8e3a86fa H) i)
end ProbabilityTheory.SimplePredictableRep


