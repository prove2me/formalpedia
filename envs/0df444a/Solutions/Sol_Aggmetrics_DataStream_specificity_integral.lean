-- Prove2me | solution 1 for Aggmetrics.DataStream.specificity_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:34.712469+00:00
-- url     : https://prove2.me/submissions/ba25bd99-5522-42dd-8415-e5c8adc53990

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_cell_ratio_prior_invariant


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {X : Type*} [MeasurableSpace X] (P0 : Measure X)
    [IsProbabilityMeasure P0] (f : X → ℝ) (hf : Integrable f P0) (π : ℝ) (hπ : π ≠ 1) :
    ((1 - π) * ∫ x, (1 - f x) ∂P0)
        / ((1 - π) * ∫ x, (1 - f x) ∂P0 + (1 - π) * ∫ x, f x ∂P0) = ∫ x, (1 - f x) ∂P0 := by
  have h : ∫ x, f x ∂P0 = 1 - ∫ x, (1 - f x) ∂P0 := by
    rw [integral_sub (integrable_const 1) hf]
    simp
  rw [h]
  exact cell_ratio_prior_invariant (1 - π) _ (sub_ne_zero.mpr (Ne.symm hπ))
end Aggmetrics.DataStream
