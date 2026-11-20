-- Prove2me | solution 1 for Aggmetrics.DataStream.fading_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:45.155398+00:00
-- url     : https://prove2.me/submissions/3dfcd7bb-20fd-44be-b962-0ef0a52885ce

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_sum


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hint : ∀ k, Integrable (X k) μ) (c : ℝ)
    (hmean : ∀ k, ∫ ω, X k ω ∂μ = c) (α : ℝ) (t : ℕ) :
    ∫ ω, ∑ k ∈ range t, fadeWeight α t k * X k ω ∂μ = (1 - α ^ t) * c := by
  rw [integral_finsetSum _ (fun k _ => (hint k).const_mul _)]
  simp_rw [integral_const_mul, hmean]
  rw [← Finset.sum_mul, fadeWeight_sum]
end Aggmetrics.DataStream
