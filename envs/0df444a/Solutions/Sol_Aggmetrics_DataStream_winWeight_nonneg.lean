-- Prove2me | solution 1 for Aggmetrics.DataStream.winWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:57.449033+00:00
-- url     : https://prove2.me/submissions/86604119-5503-432b-80f4-a75ff8c5b82e

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (W n k : ℕ) : 0 ≤ winWeight W n k := by
  unfold winWeight
  split_ifs <;> positivity
end Aggmetrics.DataStream
