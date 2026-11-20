-- Prove2me | solution 1 for Aggmetrics.DataStream.window_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:05:59.536523+00:00
-- url     : https://prove2.me/submissions/b1fc51da-4cd8-4704-9bfd-c6c4c1ee858f

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStreamTemporal

set_option autoImplicit true
open Finset Matrix
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} {W n : ℕ} (hW : 0 < W) (hWn : W ≤ n) (y p : ℕ → Fin m → ℝ) :
    winState W y p (n + 1)
      = winState W y p n + (1 / (W : ℝ)) • (outer (y n) (p n) - outer (y (n - W)) (p (n - W))) := by
  unfold winState
  rw [Finset.sum_range_succ]
  have hstep : ∀ k ∈ range n, winWeight W (n + 1) k • outer (y k) (p k)
      = winWeight W n k • outer (y k) (p k)
        - (if k = n - W then (1 / (W : ℝ)) • outer (y k) (p k) else 0) := by
    intro k hk
    unfold winWeight
    by_cases h1 : k = n - W
    · subst h1
      have e1 : ¬ (n + 1 - W ≤ n - W) := by omega
      have e2 : n - W ≤ n - W := le_refl _
      simp [e1, e2]
    · have : (n + 1 - W ≤ k) ↔ (n - W ≤ k) := by omega
      by_cases h2 : n - W ≤ k
      · simp [this.mpr h2, h2, h1]
      · simp [(not_congr this).mpr h2, h2, h1]
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hmem : n - W ∈ range n := Finset.mem_range.mpr (by omega)
  rw [if_pos hmem]
  have hlast : winWeight W (n + 1) n = 1 / (W : ℝ) := by
    unfold winWeight
    rw [if_pos (by omega)]
  rw [hlast, smul_sub]
  abel
end Aggmetrics.DataStream
