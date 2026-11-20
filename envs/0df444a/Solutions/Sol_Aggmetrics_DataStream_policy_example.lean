-- Prove2me | solution 1 for Aggmetrics.DataStream.policy_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:54.06753+00:00
-- url     : https://prove2.me/submissions/8b1fc8b0-14d7-4523-9be2-0259c1ff8426

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
import Theorems.Thm_Aggmetrics_DataStream_macroNan_none

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution :
    macroExclude ![true, true, false] ![1, 2 / 3, 0] = some (5 / 6) ∧
    macroZero ![true, true, false] ![1, 2 / 3, 0] = some (5 / 9) ∧
    macroNan ![true, true, false] ![1, 2 / 3, 0] = none := by
  have hact : active ![true, true, false] = 2 := by decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [macroExclude, hact]
    norm_num [Fin.sum_univ_three, Matrix.cons_val_two]
  · simp only [macroZero]
    norm_num [Fin.sum_univ_three, Matrix.cons_val_two]
  · exact macroNan_none _ _ ⟨2, rfl⟩
end Aggmetrics.DataStream
