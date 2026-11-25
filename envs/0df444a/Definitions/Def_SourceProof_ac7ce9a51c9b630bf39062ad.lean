-- Prove2me | Definitions.Def_SourceProof_ac7ce9a51c9b630bf39062ad
-- name    : SourceProof_ac7ce9a51c9b630bf39062ad
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:38:43.476841+00:00
-- url     : https://prove2.me/theorems/db378476-9ca2-5a19-b8c4-86888e84d34d
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_removeEmptyIntervals

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Normalization_F000
import Definitions.Def_SourceProof_992fdf07bd2378bc3aafe3c8
import Definitions.Def_SourceProof_f1dc368dba361aa17c9bfbeb

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

theorem _root_.Prove2MeSourceProof.h_ac7ce9a51c9b630bf39062ad (H : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    H.removeEmptyIntervals.integral X = H.integral X :=
  (_root_.Prove2MeSourceProof.h_f1dc368dba361aa17c9bfbeb H.removeEmptyIntervals) H (_root_.Prove2MeSourceProof.h_992fdf07bd2378bc3aafe3c8 H) X
end ProbabilityTheory.SimplePredictableRep


