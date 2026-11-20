-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:41.608517+00:00
-- url     : https://prove2.me/submissions/4c094840-7b0d-41f1-b359-f7d72abcca7e

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) (r s : Fin 2) :
    classTable C j r s = ∑ b, (∑ a, sel j r a * C a b) * sel j s b := by
  simp [classTable, Matrix.mul_apply, Matrix.transpose_apply]
end Aggmetrics.DataStream
