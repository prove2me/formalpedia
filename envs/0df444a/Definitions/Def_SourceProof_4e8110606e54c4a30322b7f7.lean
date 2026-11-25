-- Prove2me | Definitions.Def_SourceProof_4e8110606e54c4a30322b7f7
-- name    : SourceProof_4e8110606e54c4a30322b7f7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:08.638655+00:00
-- url     : https://prove2.me/theorems/c0a9afcd-39cb-5d79-b98c-104838ea8242
-- title:
--   StochLean source theorem: StochLean.stieltjesJumpPart_eq_tsum

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_4e2804bfc01162ec6c386f31
import Definitions.Def_SourceProof_d525a237722b981ed0b6d6ee

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The jump part is the actual sum of positive-time jumps

The sum is indexed by every time in `(0,t]`, not an assumed enumeration of
jumps. Countable support and finite mass on compact intervals give summability.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_4e8110606e54c4a30322b7f7 (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    stieltjesJumpPart f t = ∑' s : Ioc 0 t, (f s - leftLim f s) := by
  have h := congrArg ENNReal.toReal (_root_.Prove2MeSourceProof.h_4e2804bfc01162ec6c386f31 f t)
  have hnonneg : 0 ≤ StochLean.stieltjesJumpPart f t := by
    rw [← _root_.Prove2MeSourceProof.h_d525a237722b981ed0b6d6ee f]
    exact (StochLean.stieltjesJumpPart f).mono (show (0 : ℝ≥0) ≤ t from bot_le)
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)] at h
  simpa only [ENNReal.toReal_ofReal hnonneg,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono.leftLim_le le_rfl))] using h
end StochLean


