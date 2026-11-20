-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:44.960127+00:00
-- url     : https://prove2.me/submissions/407ec0e6-81e4-4bbf-b366-95be546726bc

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α : ℝ) (n : ℕ) : fadeWeight α (n + 1) n = 1 - α := by
  simp [fadeWeight]
end Aggmetrics.DataStream
