-- Prove2me | Definitions.Def_SourceProof_dfa9835b65113f9bb1f932de
-- name    : SourceProof_dfa9835b65113f9bb1f932de
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:57:46.626272+00:00
-- url     : https://prove2.me/theorems/f7dae223-86e9-4180-b9ea-335eeb789993
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurableSet_inter_gt_before

import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000

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

theorem _root_.Prove2MeSourceProof.h_dfa9835b65113f9bb1f932de (hτ : IsStoppingTime F τ) (t : ℝ≥0)
    {A : Set Ω} (hA : MeasurableSet[F t] A) :
    MeasurableSet[hτ.measurableSpaceBefore] (A ∩ {ω | (t : WithTop ℝ≥0) < τ ω}) :=
  (show MeasurableSpace.generateFrom _ ≤ hτ.measurableSpaceBefore from le_sup_right) _
    (MeasurableSpace.measurableSet_generateFrom ⟨t, A, hA, rfl⟩)
end MeasureTheory.IsStoppingTime


