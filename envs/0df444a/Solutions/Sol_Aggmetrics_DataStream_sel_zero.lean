-- Prove2me | solution 1 for Aggmetrics.DataStream.sel_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:46.661183+00:00
-- url     : https://prove2.me/submissions/0663082c-c01b-4dc9-9387-bad4c00a0f14

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (j l : Fin m) : sel j 0 l = if l = j then 1 else 0 := by simp [sel]
end Aggmetrics.DataStream
