-- Prove2me | Definitions.Def_SourceProof_412e9d867e05f3b1c89be57a
-- name    : SourceProof_412e9d867e05f3b1c89be57a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:57.9784+00:00
-- url     : https://prove2.me/theorems/baa14f35-0d81-4bfd-b2b2-307cae2d7091
-- title:
--   StochLean source theorem: StochLean.integral_eq_tsum_of_countable_support

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrals of countably supported functions on uncountable spaces -/

@[expose] public section

open MeasureTheory Set Function

namespace StochLean

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ : Measure α} {f : α → ℝ}

theorem _root_.Prove2MeSourceProof.h_412e9d867e05f3b1c89be57a (hc : (support f).Countable)
    (hf : Integrable f μ) : ∫ t, f t ∂μ = ∑' t, μ.real {t} * f t := by
  calc
    _ = ∫ t in support f, f t ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ ht ↦ not_not.mp ht)).symm
    _ = ∑' t : support f, μ.real {(t : α)} * f t := by
      simpa only [smul_eq_mul] using setIntegral_countable f hc hf.integrableOn
    _ = ∑' t, μ.real {t} * f t := by
      apply tsum_subtype_eq_of_support_subset (f := fun t : α ↦ μ.real {t} * f t)
        (s := support f)
      intro t ht hf0
      exact ht (by
        change μ.real {t} * f t = 0
        rw [hf0, mul_zero])
end StochLean


