-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeWeight_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:17:44.264639+00:00
-- url     : https://prove2.me/submissions/25c74c69-c5eb-4e0d-b808-4a013ab23abc

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α : ℝ} {n k : ℕ} (hk : k < n) :
    fadeWeight α (n + 1) k = α * fadeWeight α n k := by
  unfold fadeWeight
  have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
  rw [this, pow_succ]
  ring
end Aggmetrics.DataStream
