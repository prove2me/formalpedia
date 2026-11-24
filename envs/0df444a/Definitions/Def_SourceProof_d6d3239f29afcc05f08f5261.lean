-- Prove2me | Definitions.Def_SourceProof_d6d3239f29afcc05f08f5261
-- name    : SourceProof_d6d3239f29afcc05f08f5261
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:26.860019+00:00
-- url     : https://prove2.me/theorems/8d3ba167-975d-43d8-80a7-e4706419aaf3
-- title:
--   StochLean source theorem: MeasureTheory.IsStoppingTime.measurable_before

import Definitions.Def_SourceProof_963ead9a91977c0b480ddda0

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

theorem _root_.Prove2MeSourceProof.h_d6d3239f29afcc05f08f5261 (hτ : IsStoppingTime F τ) :
    Measurable[hτ.measurableSpaceBefore] τ := by
  apply measurable_of_Ioi
  intro t
  cases t with
  | top => simp
  | coe t => exact (_root_.Prove2MeSourceProof.h_963ead9a91977c0b480ddda0 hτ) t
end MeasureTheory.IsStoppingTime


