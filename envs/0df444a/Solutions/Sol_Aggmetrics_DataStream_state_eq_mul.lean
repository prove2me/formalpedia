-- Prove2me | solution 1 for Aggmetrics.DataStream.state_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:15.505917+00:00
-- url     : https://prove2.me/submissions/3a7ac60a-02a8-4fb0-a640-c64cd4eb6585

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_state_apply

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) :
    state w y p = (Matrix.of y)ᵀ * Matrix.diagonal w * Matrix.of p := by
  ext a b
  simp [state_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]
end Aggmetrics.DataStream
