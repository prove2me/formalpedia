-- Prove2me | solution 1 for Aggmetrics.DataStream.winWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:57.950804+00:00
-- url     : https://prove2.me/submissions/ae0fa3da-b634-47ce-8ccd-2b829ef8be9b

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) :
    ∑ k ∈ range n, winWeight W n k = 1 := by
  unfold winWeight
  rw [← Finset.sum_filter]
  have hf : (range n).filter (fun k => n - W ≤ k) = Ico (n - W) n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have : n - (n - W) = W := by omega
  rw [this]
  have hW' : (W : ℝ) ≠ 0 := by positivity
  field_simp
end Aggmetrics.DataStream
