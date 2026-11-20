-- Prove2me | solution 1 for Aggmetrics.DataStream.sel_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:45.847362+00:00
-- url     : https://prove2.me/submissions/ffee956f-d201-45fe-a312-f4f2e68884e6

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (j l : Fin m) : sel j 1 l = if l = j then 0 else 1 := by simp [sel]
end Aggmetrics.DataStream
