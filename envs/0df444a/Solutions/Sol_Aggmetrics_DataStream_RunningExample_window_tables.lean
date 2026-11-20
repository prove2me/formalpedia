-- Prove2me | solution 1 for Aggmetrics.DataStream.RunningExample.window_tables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:23.689567+00:00
-- url     : https://prove2.me/submissions/6aad4c83-5bb0-4121-b3ad-9dee5aeaf721

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamExample
import Theorems.Thm_Aggmetrics_DataStream_RunningExample_window_state_eight

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream Aggmetrics.DataStream.RunningExample
namespace Aggmetrics.DataStream.RunningExample
theorem _root_.solution :
    classTable (winState 4 y p 8) 0 = !![1 / 4, 0; 0, 3 / 4] ∧
    classTable (winState 4 y p 8) 1 = !![1 / 2, 1 / 4; 0, 1 / 4] ∧
    classTable (winState 4 y p 8) 2 = !![0, 0; 1 / 4, 3 / 4] := by
  rw [window_state_eight]
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext r s
    fin_cases r <;> fin_cases s <;>
      simp [classTable, sel, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num
end Aggmetrics.DataStream.RunningExample
