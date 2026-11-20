-- Prove2me | solution 1 for Aggmetrics.DataStream.classTable_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:58:56.412389+00:00
-- url     : https://prove2.me/submissions/2f1b4cfe-5e52-43d3-b0eb-0e190b13afa3

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (c : Fin n → ℝ) (C : Fin n → Matrix (Fin m) (Fin m) ℝ) (j : Fin m) :
    classTable (∑ k, c k • C k) j = ∑ k, c k • classTable (C k) j := by
  simp [classTable, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
end Aggmetrics.DataStream
