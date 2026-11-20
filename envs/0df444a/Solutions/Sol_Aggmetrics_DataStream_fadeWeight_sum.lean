-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:04:27.758203+00:00
-- url     : https://prove2.me/submissions/9e272003-57cc-4ba5-87a8-819fb2d8d38f

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α : ℝ) (n : ℕ) : ∑ k ∈ range n, fadeWeight α n k = 1 - α ^ n := by
  unfold fadeWeight
  rw [← Finset.mul_sum]
  have h := Finset.sum_range_reflect (fun j => α ^ j) n
  rw [h, mul_comm]
  exact geom_sum_mul_neg α n
end Aggmetrics.DataStream
