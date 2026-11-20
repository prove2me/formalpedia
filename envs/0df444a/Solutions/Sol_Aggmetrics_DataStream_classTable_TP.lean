-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_TP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:31.722248+00:00
-- url     : https://prove2.me/submissions/4744dadb-b30f-4987-9b9b-afcaa7cce918

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable C j 0 0 = C j j := by
  simp [classTable, sel, Matrix.mul_apply, Matrix.transpose_apply]
end Aggmetrics.DataStream
