-- Prove2me | Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002
-- name    : StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:12.075809+00:00
-- url     : https://prove2.me/theorems/7ea25a78-7657-4fa2-b3bf-d9408ccbbd73
-- title:
--   StochLean: ForMathlib.MeasureTheory.PointAtomicDecomposition F002

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F001

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

instance pointDiffusePart_nullSingletonClass (μ : Measure T) :
    NullSingletonClass (pointDiffusePart μ) := by
  classical
  refine ⟨fun t ↦ ?_⟩
  rw [pointDiffusePart, Measure.restrict_apply (measurableSet_singleton t)]
  by_cases ht : t ∈ pointAtomSet μ
  · rw [singleton_inter_eq_empty.mpr (show t ∉ (pointAtomSet μ)ᶜ from fun hc ↦ hc ht),
      measure_empty]
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ht)]
    exact not_not.mp ht
end StochLean


