-- Prove2me | solution 1 for Aggmetrics.DataStream.state_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:01:45.86155+00:00
-- url     : https://prove2.me/submissions/2e77f846-ed2c-40cf-9823-60d526b337b1

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal
import Theorems.Thm_Aggmetrics_DataStream_state_apply

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} {w : Fin n → ℝ} (hw : ∀ k, 0 ≤ w k) {y p : Fin n → Fin m → ℝ}
    (hy : ∀ k a, 0 ≤ y k a) (hp : ∀ k a, 0 ≤ p k a) (a b : Fin m) : 0 ≤ state w y p a b := by
  rw [state_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (mul_nonneg (hy k a) (hp k b))
end Aggmetrics.DataStream
