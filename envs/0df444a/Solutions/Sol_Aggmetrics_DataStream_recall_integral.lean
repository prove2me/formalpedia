-- Prove2me | solution 1 for Aggmetrics.DataStream.recall_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:23.866422+00:00
-- url     : https://prove2.me/submissions/fb9c3dbb-3717-4b1d-9010-1c6c11b63d03

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_cell_ratio_prior_invariant


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {X : Type*} [MeasurableSpace X] (P1 : Measure X) [IsProbabilityMeasure P1]
    (f : X → ℝ) (hf : Integrable f P1) (π : ℝ) (hπ : π ≠ 0) :
    (π * ∫ x, f x ∂P1) / (π * ∫ x, f x ∂P1 + π * ∫ x, (1 - f x) ∂P1) = ∫ x, f x ∂P1 := by
  have h : ∫ x, (1 - f x) ∂P1 = 1 - ∫ x, f x ∂P1 := by
    rw [integral_sub (integrable_const 1) hf]
    simp
  rw [h]
  exact cell_ratio_prior_invariant π _ hπ
end Aggmetrics.DataStream
