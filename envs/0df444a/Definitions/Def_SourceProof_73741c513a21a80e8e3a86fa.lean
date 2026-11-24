-- Prove2me | Definitions.Def_SourceProof_73741c513a21a80e8e3a86fa
-- name    : SourceProof_73741c513a21a80e8e3a86fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:11.897114+00:00
-- url     : https://prove2.me/theorems/9be7962b-5fd5-4d51-a7fa-3b327e366466
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.measurableSet_strictInterval

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003

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

theorem _root_.Prove2MeSourceProof.h_73741c513a21a80e8e3a86fa (H : SimplePredictableRep F) (i : Fin H.partition.size) :
    MeasurableSet[(H.partition.point i.castSucc).measurableSpace]
      {ω | H.partition.point i.castSucc ω < H.partition.point i.succ ω} := by
  simpa only [Set.compl_ofPred, WithTop.coe_le_coe, not_le] using
    ((H.partition.point i.succ).isStoppingTime.measurableSet_stopping_time_le
      (H.partition.point i.castSucc).isStoppingTime).compl
end ProbabilityTheory.SimplePredictableRep


