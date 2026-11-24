-- Prove2me | Definitions.Def_SourceProof_963ead9a91977c0b480ddda0
-- name    : SourceProof_963ead9a91977c0b480ddda0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:31.296856+00:00
-- url     : https://prove2.me/theorems/aa90f267-3dcc-40b7-b911-bfac2f09cc0f
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSet_gt_before

import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000
import Definitions.Def_SourceProof_dfa9835b65113f9bb1f932de

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The sigma-field strictly before a stopping time

Protter III.2 defines `F_{T-}` using `F_0` and the events `A ∩ {t < T}`,
where `A ∈ F_t` and `t > 0`. We allow `t = 0` in the sole owner below and
prove that this gives exactly the same sigma-field. This is a subfield of
Mathlib's existing stopped sigma-field, not a replacement for it.

At infinite lifetime this field is `⨆ t, F t`, not necessarily `F_0` or
the ambient sigma-field. No process value at infinity is defined here.
-/

@[expose] public section

open Set
open scoped NNReal

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {τ : Ω → WithTop ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_963ead9a91977c0b480ddda0 (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    MeasurableSet[hτ.measurableSpaceBefore] {ω | (t : WithTop ℝ≥0) < τ ω} := by
  simpa only [univ_inter] using (_root_.Prove2MeSourceProof.h_dfa9835b65113f9bb1f932de hτ) t MeasurableSet.univ
end MeasureTheory.IsStoppingTime


