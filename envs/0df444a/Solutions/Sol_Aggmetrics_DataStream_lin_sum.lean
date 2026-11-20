-- Prove2me | solution 1 for Aggmetrics.DataStream.lin_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:59:17.397304+00:00
-- url     : https://prove2.me/submissions/5661aae2-b95f-4882-9e55-9dbd3ba1da24

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (a : Fin 4 → ℝ) (T : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    lin a (∑ j, T j) = ∑ j, lin a (T j) := by
  simp [lin, Matrix.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]
end Aggmetrics.DataStream
