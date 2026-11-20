-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:18.929513+00:00
-- url     : https://prove2.me/submissions/2cf8852a-b03b-4d92-a1f8-42a7ebb69981

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction

set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) {n n' k : ℕ} (hnn : n ≤ n') :
    fadeWeight α n' k ≤ fadeWeight α n k := by
  unfold fadeWeight
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  exact pow_le_pow_of_le_one h0 h1 (by omega)
end Aggmetrics.DataStream
