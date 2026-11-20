-- Prove2me | solution 1 for Aggmetrics.DataStream.lost_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:23:17.847606+00:00
-- url     : https://prove2.me/submissions/f1afa732-76c4-448d-aee1-c829e4d9e9c3

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction

set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop) (arr : ℕ → ℕ)
    (n : ℕ) (a b : Fin m) :
    (lostState α ε y yt p aud arr n) a b
      = ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k),
          fadeWeight α n k * ((y k a - yt k a) * p k b) := by
  unfold lostState
  rw [Matrix.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : discarded α ε aud arr n k
  · simp only [h, if_true, Matrix.smul_apply, Matrix.sub_apply, outer, Matrix.of_apply,
      smul_eq_mul]
    ring
  · simp [h]
end Aggmetrics.DataStream
