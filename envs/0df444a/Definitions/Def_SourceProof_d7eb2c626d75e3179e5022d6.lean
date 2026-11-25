-- Prove2me | Definitions.Def_SourceProof_d7eb2c626d75e3179e5022d6
-- name    : SourceProof_d7eb2c626d75e3179e5022d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:25.806785+00:00
-- url     : https://prove2.me/theorems/d4bf22b7-b4af-40de-bd5c-d501dff1f224
-- title:
--   StochLean source theorem: StochLean.pointDiffusePart_restrict

import Definitions.Def_SourceProof_c76249a292da67937efb1fa8

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Point-diffuse restriction depends only on the restricted measure -/

@[expose] public section

open MeasureTheory Set

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

theorem _root_.Prove2MeSourceProof.h_d7eb2c626d75e3179e5022d6 (μ : Measure T) {s : Set T} (hs : MeasurableSet s) :
    pointDiffusePart (μ.restrict s) = (pointDiffusePart μ).restrict s := by
  rw [StochLean.pointDiffusePart, _root_.Prove2MeSourceProof.h_c76249a292da67937efb1fa8, Measure.restrict_restrict' hs,
    StochLean.pointDiffusePart, Measure.restrict_restrict hs]
  congr 1
  ext t
  simp only [mem_inter_iff, mem_compl_iff]
  tauto
end StochLean


