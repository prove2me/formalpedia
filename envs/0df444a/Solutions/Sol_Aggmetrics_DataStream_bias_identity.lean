-- Prove2me | solution 1 for Aggmetrics.DataStream.bias_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:00.220176+00:00
-- url     : https://prove2.me/submissions/6f02f152-bc21-4f98-bc82-56074999e2e0

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay
import Theorems.Thm_Aggmetrics_DataStream_state_apply


set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ) :
    state w y p - unified w O y yt p
      = ∑ k, ((1 - O k) * w k) • outer (fun c => y k c - yt k c) (p k) := by
  ext a b
  simp only [unified, state_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
  rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)
end Aggmetrics.DataStream
