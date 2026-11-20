-- Prove2me | solution 1 for Aggmetrics.DataStream.RunningExample.window_state_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:01:47.612385+00:00
-- url     : https://prove2.me/submissions/328e4ee7-bbbe-4cfc-b2fb-7c0102c7596a

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample
namespace Aggmetrics.DataStream.RunningExample
theorem _root_.solution :
    winState 4 y p 8 = !![1 / 4, 0, 0; 0, 1 / 2, 1 / 4; 0, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [winState, winWeight, Finset.sum_range_succ, outer, y, p, lab, pre] <;> norm_num
end Aggmetrics.DataStream.RunningExample
