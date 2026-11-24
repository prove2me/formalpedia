-- Prove2me | Definitions.Def_SourceProof_3b0f7c2a9d38ed7556f52fb8
-- name    : SourceProof_3b0f7c2a9d38ed7556f52fb8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:58:37.520981+00:00
-- url     : https://prove2.me/theorems/12a6fa61-bfc2-402b-b1cc-315df1551ac9
-- title:
--   StochLean source theorem: StochLean.pointAtomicPart_apply

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001
import Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The point-atomic and point-diffuse parts of an s-finite measure

The countable set of positive-mass singletons is intrinsic. Restriction to it
and to its complement gives the decomposition. On general measurable spaces,
having no point atoms is not asserted to exclude all nonsingleton atoms.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]

theorem _root_.Prove2MeSourceProof.h_3b0f7c2a9d38ed7556f52fb8 (μ : Measure T) [SFinite μ] {s : Set T} (hs : MeasurableSet s) :
    pointAtomicPart μ s = ∑' t : ↥(s ∩ pointAtomSet μ), μ {(t : T)} := by
  rw [StochLean.pointAtomicPart, Measure.restrict_apply hs]
  have hc : (s ∩ StochLean.pointAtomSet μ).Countable := (_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd μ).mono inter_subset_right
  simpa only [preimage_id] using
    (tsum_measure_preimage_singleton (μ := μ) hc (f := id)
      (fun t _ ↦ measurableSet_singleton t)).symm
end StochLean


