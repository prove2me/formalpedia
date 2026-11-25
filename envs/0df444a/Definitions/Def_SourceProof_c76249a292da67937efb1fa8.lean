-- Prove2me | Definitions.Def_SourceProof_c76249a292da67937efb1fa8
-- name    : SourceProof_c76249a292da67937efb1fa8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:07.843804+00:00
-- url     : https://prove2.me/theorems/47e51f2b-b301-44f4-bf13-e1832a2d2188
-- title:
--   StochLean source theorem: StochLean.pointAtomSet_restrict

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002

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

theorem _root_.Prove2MeSourceProof.h_c76249a292da67937efb1fa8 (μ : Measure T) (s : Set T) :
    pointAtomSet (μ.restrict s) = s ∩ pointAtomSet μ := by
  classical
  ext t
  change (μ.restrict s) {t} ≠ 0 ↔ t ∈ s ∧ μ {t} ≠ 0
  rw [Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : t ∈ s
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ht)]
    simp only [ht, true_and]
  · rw [singleton_inter_eq_empty.mpr ht, measure_empty]
    simp only [ht, false_and, ne_eq, not_true_eq_false]
end StochLean


