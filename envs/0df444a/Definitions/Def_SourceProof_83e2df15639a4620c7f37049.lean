-- Prove2me | Definitions.Def_SourceProof_83e2df15639a4620c7f37049
-- name    : SourceProof_83e2df15639a4620c7f37049
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:26:06.151439+00:00
-- url     : https://prove2.me/theorems/09254822-f152-43a7-a8f0-d0c9890a4a62
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.isCagladPath

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F003
import Definitions.Def_SourceProof_2749954deff006f85600afa1
import Definitions.Def_SourceProof_2788bc818189572242b6cda6
import Definitions.Def_SourceProof_5a54fb45dc4f9dd0bdee1f91
import Definitions.Def_SourceProof_f90bd334d926b7a0f3f6f377
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source simple predictable processes really are adapted, caglad and predictable

Coefficient measurability is used at the original left stopping endpoint. Neither
bounded coefficients nor strict separation of endpoints is assumed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_83e2df15639a4620c7f37049 (H : SimplePredictableRep F) (ω : Ω) :
    IsCagladPath (fun t ↦ H.toProcess t ω) := by
  have hsum := _root_.Prove2MeSourceProof.h_2749954deff006f85600afa1 Finset.univ
    (fun i : Fin H.partition.size ↦ fun t : ℝ≥0 ↦
      if H.partition.point i.castSucc ω < t ∧ t ≤ H.partition.point i.succ ω
      then H.coefficient i ω else 0)
    (fun i _ ↦ _root_.Prove2MeSourceProof.h_5a54fb45dc4f9dd0bdee1f91 ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) i) (H.coefficient i ω))
  have h := (_root_.Prove2MeSourceProof.h_2788bc818189572242b6cda6 (_root_.Prove2MeSourceProof.h_f90bd334d926b7a0f3f6f377 (H.initial ω))) hsum
  convert h using 1
  funext t
  change (if t = 0 then H.initial ω else _) = (if t = 0 then H.initial ω else 0) + _
  by_cases ht : t = 0
  · subst t
    have hzero (i : Fin H.partition.size) : ¬ H.partition.point i.castSucc ω < 0 :=
      not_lt_of_ge bot_le
    simp only [hzero, false_and, if_false, Finset.sum_const_zero, add_zero]
  · simp only [if_neg ht, zero_add]
end SimplePredictableRep

end ProbabilityTheory


