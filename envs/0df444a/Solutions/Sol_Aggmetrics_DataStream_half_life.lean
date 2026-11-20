-- Prove2me | solution 1 for Aggmetrics.DataStream.half_life
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:53.816416+00:00
-- url     : https://prove2.me/submissions/05d2275a-a1c4-4beb-99dc-9cb539606f09

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_window_sizing_rule


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α : ℝ) (h0 : 0 < α) (h1 : α < 1) (s : ℕ)
    (hs : (s : ℝ) ≥ Real.log 2 / (-Real.log α)) : α ^ s ≤ 1 / 2 := by
  have e : Real.log (1 / (1 / 2 : ℝ)) / (-Real.log (1 - (1 - α))) = Real.log 2 / (-Real.log α) := by
    rw [one_div_one_div, sub_sub_cancel]
  have h := window_sizing_rule (1 - α) (1 / 2) (by linarith) (by linarith) (by norm_num) s
    (by rw [e]; exact hs)
  rwa [sub_sub_cancel] at h
end Aggmetrics.DataStream
