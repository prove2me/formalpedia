-- Prove2me | solution 1 for Aggmetrics.DataStream.RunningExample.fade_state_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:06:01.144046+00:00
-- url     : https://prove2.me/submissions/333f4201-e96f-45fa-83a1-6d5173efe739

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample
namespace Aggmetrics.DataStream.RunningExample
theorem _root_.solution :
    fadeState (1 / 2) y p 4 = !![1 / 16, 1 / 4, 0; 0, 1 / 8, 0; 0, 0, 1 / 2] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fadeState, outer, y, p, lab, pre] <;> norm_num
end Aggmetrics.DataStream.RunningExample
