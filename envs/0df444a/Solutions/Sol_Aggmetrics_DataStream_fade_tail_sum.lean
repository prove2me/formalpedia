-- Prove2me | solution 1 for Aggmetrics.DataStream.fade_tail_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:02.021201+00:00
-- url     : https://prove2.me/submissions/f702081a-d446-4fb5-bf43-6bd971be747c

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (s : ℕ) :
    HasSum (fun j : ℕ => (1 - α) * α ^ (s + j)) (α ^ s) := by
  have hne : (1 - α) ≠ 0 := by linarith
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_left ((1 - α) * α ^ s)
  convert h using 1 <;> try rfl
  · ext j
    rw [pow_add]
    ring
  · field_simp
end Aggmetrics.DataStream
