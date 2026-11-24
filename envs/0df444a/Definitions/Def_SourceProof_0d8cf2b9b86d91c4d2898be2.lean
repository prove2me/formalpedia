-- Prove2me | Definitions.Def_SourceProof_0d8cf2b9b86d91c4d2898be2
-- name    : SourceProof_0d8cf2b9b86d91c4d2898be2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:39.040896+00:00
-- url     : https://prove2.me/theorems/6183769d-3cf1-4b10-b1b0-35d29fefd368
-- title:
--   StochLean source theorem: StochLean.setIntegral_eq_tsum_of_countable_support

import Definitions.Def_SourceProof_412e9d867e05f3b1c89be57a

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

theorem _root_.Prove2MeSourceProof.h_0d8cf2b9b86d91c4d2898be2 (hc : (support f).Countable)
    {s : Set α} (hs : MeasurableSet s) (hf : IntegrableOn f s μ) :
    ∫ t in s, f t ∂μ = ∑' t : s, μ.real {(t : α)} * f t := by
  classical
  have hc' : (support (s.indicator f)).Countable := hc.mono (by
    intro t ht hf0
    by_cases hts : t ∈ s
    · exact ht (by rw [indicator_of_mem hts, hf0])
    · exact ht (indicator_of_notMem hts f))
  calc
    _ = ∫ t, s.indicator f t ∂μ := (integral_indicator hs).symm
    _ = ∑' t, μ.real {t} * s.indicator f t :=
      _root_.Prove2MeSourceProof.h_412e9d867e05f3b1c89be57a hc' (hf.integrable_indicator hs)
    _ = ∑' t, s.indicator (fun u ↦ μ.real {u} * f u) t := by
      apply tsum_congr
      intro t
      by_cases ht : t ∈ s
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
    _ = ∑' t : s, μ.real {(t : α)} * f t := (tsum_subtype s _).symm
end StochLean


