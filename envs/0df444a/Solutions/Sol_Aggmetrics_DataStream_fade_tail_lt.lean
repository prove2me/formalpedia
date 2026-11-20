-- Prove2me | solution 1 for Aggmetrics.DataStream.fade_tail_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:02.618197+00:00
-- url     : https://prove2.me/submissions/3908cede-be46-4e5f-88d9-2036b5e9a377

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α ε : ℝ} (h1 : α < 1) (s : ℕ) (hs : (1 - α) * α ^ s < ε) :
    α ^ s < ε * (1 / (1 - α)) := by
  have hpos : 0 < 1 - α := by linarith
  rw [mul_one_div, lt_div_iff₀ hpos, mul_comm]
  exact hs
end Aggmetrics.DataStream
