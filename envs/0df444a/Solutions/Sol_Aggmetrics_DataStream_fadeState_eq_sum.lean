-- Prove2me | solution 1 for Aggmetrics.DataStream.fadeState_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:00:38.208078+00:00
-- url     : https://prove2.me/submissions/16d798fc-3ce4-4be8-8ee6-421afb1e5213

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α : ℝ) (y p : ℕ → Fin m → ℝ) (n : ℕ) :
    fadeState α y p n = ∑ k ∈ range n, fadeWeight α n k • outer (y k) (p k) := by
  induction n with
  | zero => simp [fadeState]
  | succ n ih =>
    rw [fadeState, ih, Finset.sum_range_succ, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < n := Finset.mem_range.mp hk
      rw [smul_smul]
      congr 1
      unfold fadeWeight
      have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [this, pow_succ]
      ring
    · simp [fadeWeight]
end Aggmetrics.DataStream
