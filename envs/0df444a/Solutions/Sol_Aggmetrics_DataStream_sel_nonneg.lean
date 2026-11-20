-- Prove2me | solution 1 for Aggmetrics.DataStream.sel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:59:06.400069+00:00
-- url     : https://prove2.me/submissions/63d145e3-3452-42d7-beff-ff486cad1d84

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (j : Fin m) (r : Fin 2) (l : Fin m) : 0 ≤ sel j r l := by
  simp only [sel, Matrix.of_apply]
  split_ifs <;> norm_num
end Aggmetrics.DataStream
