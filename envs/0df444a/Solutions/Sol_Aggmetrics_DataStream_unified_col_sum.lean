-- Prove2me | solution 1 for Aggmetrics.DataStream.unified_col_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:01.353171+00:00
-- url     : https://prove2.me/submissions/08f5863c-dbf9-4aa9-8f63-025a5fd6004e

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m n : ℕ} (w O : Fin n → ℝ) (y yt p : Fin n → Fin m → ℝ)
    (hy : ∀ k, ∑ a, y k a = 1) (hyt : ∀ k, ∑ a, yt k a = 1) (b : Fin m) :
    ∑ a, unified w O y yt p a b = ∑ k, w k * p k b := by
  have h : ∀ a, unified w O y yt p a b
      = ∑ k, ((O k * w k) * (y k a * p k b) + ((1 - O k) * w k) * (yt k a * p k b)) := by
    intro a
    simp only [unified, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, outer,
      Matrix.of_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  calc ∑ a, ((O k * w k) * (y k a * p k b) + ((1 - O k) * w k) * (yt k a * p k b))
      = (O k * w k * p k b) * ∑ a, y k a + ((1 - O k) * w k * p k b) * ∑ a, yt k a := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun a _ => by ring)
    _ = w k * p k b := by rw [hy k, hyt k]; ring
end Aggmetrics.DataStream
