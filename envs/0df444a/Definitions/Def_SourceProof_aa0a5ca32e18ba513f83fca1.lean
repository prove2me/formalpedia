-- Prove2me | Definitions.Def_SourceProof_aa0a5ca32e18ba513f83fca1
-- name    : SourceProof_aa0a5ca32e18ba513f83fca1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:49.733833+00:00
-- url     : https://prove2.me/theorems/dcd6654a-5d58-48e9-b075-09d0543da5b6
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.toProcess_rightEndpoint

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

theorem _root_.Prove2MeSourceProof.h_aa0a5ca32e18ba513f83fca1 (H : SimplePredictableRep F) (i : Fin H.partition.size)
    {ω : Ω} (hi : H.partition.point i.castSucc ω < H.partition.point i.succ ω) :
    H.toProcess (H.partition.point i.succ ω) ω = H.coefficient i ω := by
  have hpos : 0 < H.partition.point i.succ ω := lt_of_le_of_lt bot_le hi
  rw [ProbabilityTheory.SimplePredictableRep.toProcess, if_neg (ne_of_gt hpos)]
  rw [sum_eq_single i]
  · simp only [hi, le_refl, and_self, if_true]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · have hle : H.partition.point j.succ ω ≤ H.partition.point i.castSucc ω :=
        H.partition.monotone_point ω (show j.succ ≤ i.castSucc from hji)
      exact if_neg (fun h ↦ (not_le.mpr (hle.trans_lt hi)) h.2)
    · have hle : H.partition.point i.succ ω ≤ H.partition.point j.castSucc ω :=
        H.partition.monotone_point ω (show i.succ ≤ j.castSucc from hij)
      exact if_neg (fun h ↦ (not_lt.mpr hle) h.1)
  · simp
end ProbabilityTheory.SimplePredictableRep


