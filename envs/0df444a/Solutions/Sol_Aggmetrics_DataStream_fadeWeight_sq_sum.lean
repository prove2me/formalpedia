-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_sq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:03.80789+00:00
-- url     : https://prove2.me/submissions/6fe73cc1-92c7-4f79-919e-bdaf1de885ed

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    ∑ k ∈ range t, (fadeWeight α t k) ^ 2 = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) := by
  unfold fadeWeight
  have h := Finset.sum_range_reflect (fun j => ((1 - α) * α ^ j) ^ 2) t
  rw [h]
  have hgeo := geom_sum_mul_neg (α ^ 2) t
  have hne : (1 - α ^ 2) ≠ 0 := by nlinarith
  have hs : ∑ j ∈ range t, ((1 - α) * α ^ j) ^ 2 = (1 - α) ^ 2 * ∑ j ∈ range t, (α ^ 2) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hs, eq_div_of_mul_eq hne hgeo]
  have hα2 : (α ^ 2) ^ t = α ^ (2 * t) := by rw [← pow_mul]
  rw [hα2]
  have h1a : (1 - α) ≠ 0 := by linarith
  have h1b : (1 + α) ≠ 0 := by linarith
  have h1c : (1 - α ^ 2) = (1 - α) * (1 + α) := by ring
  rw [h1c]
  field_simp
end Aggmetrics.DataStream
