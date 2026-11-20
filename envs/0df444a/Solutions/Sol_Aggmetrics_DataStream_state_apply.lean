-- Prove2me | solution 1 for Aggmetrics.DataStream.state_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:52.888706+00:00
-- url     : https://prove2.me/submissions/0c3bda3d-f48c-4073-86f3-b52db3ed7ae8

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w : Fin n → ℝ) (y p : Fin n → Fin m → ℝ) (a b : Fin m) :
    state w y p a b = ∑ k, w k * (y k a * p k b) := by
  simp [state, outer, Matrix.sum_apply]
end Aggmetrics.DataStream
