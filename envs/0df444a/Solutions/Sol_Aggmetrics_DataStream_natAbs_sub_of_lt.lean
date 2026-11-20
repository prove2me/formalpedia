-- Prove2me | solution 1 for Aggmetrics.DataStream.natAbs_sub_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:51.809805+00:00
-- url     : https://prove2.me/submissions/7a6a5a3a-9b31-4f7f-a47b-6d98eb113a4a

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {i t : ℕ} (h : i < t) : Int.natAbs ((i : ℤ) - (t : ℤ)) = t - i := by
  have e : ((i : ℤ) - (t : ℤ)) = -((t - i : ℕ) : ℤ) := by omega
  rw [e]
  simp
end Aggmetrics.DataStream
