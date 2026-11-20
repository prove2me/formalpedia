-- Prove2me | solution 1 for Aggmetrics.DataStream.fade_Ico_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:45.319974+00:00
-- url     : https://prove2.me/submissions/bbc38d4f-be40-41a3-9e67-81f57fa6af6e

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} (s N : ℕ) (hsN : s ≤ N) :
    ∑ j ∈ Ico s N, (1 - α) * α ^ j = α ^ s - α ^ N := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ico_succ_top hN, ih]
    ring
end Aggmetrics.DataStream
