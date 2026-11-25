-- Prove2me | Definitions.Def_SourceProof_da9aca4c0192738c4fa4fc29
-- name    : SourceProof_da9aca4c0192738c4fa4fc29
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:35:37.431975+00:00
-- url     : https://prove2.me/theorems/9f1e6878-6b79-40d8-abf7-d1bf703cd1c4
-- title:
--   StochLean source theorem: StochLean.integral_pointAtomicPart_eq_tsum

import Definitions.Def_StochLean_ForMathlib_MeasureTheory_PointAtomicDecomposition_F002
import Definitions.Def_SourceProof_fc5f89aed67e82971b1326cd
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integration against the intrinsic point-atomic part

The series identity requires actual integrability. The underlying space need
not be countable: only the positive-mass singletons are counted.
-/

@[expose] public section

open MeasureTheory Set Function

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
  {μ : Measure T} [SFinite μ] {f : T → ℝ}

theorem _root_.Prove2MeSourceProof.h_da9aca4c0192738c4fa4fc29 (hf : Integrable f (pointAtomicPart μ)) :
    ∫ t, f t ∂pointAtomicPart μ = ∑' t, μ.real {t} * f t := by
  calc
    _ = ∑' t : StochLean.pointAtomSet μ, μ.real {(t : T)} * f t := by
      simpa only [StochLean.pointAtomicPart, smul_eq_mul] using
        setIntegral_countable f (_root_.Prove2MeSourceProof.h_fc5f89aed67e82971b1326cd μ) hf
    _ = ∑' t, μ.real {t} * f t := by
      apply tsum_subtype_eq_of_support_subset
        (f := fun t : T ↦ μ.real {t} * f t) (s := StochLean.pointAtomSet μ)
      intro t ht
      by_contra ha
      have hz : μ {t} = 0 := not_not.mp ha
      exact ht (by simp only [measureReal_def, hz, ENNReal.toReal_zero, zero_mul])
end StochLean


