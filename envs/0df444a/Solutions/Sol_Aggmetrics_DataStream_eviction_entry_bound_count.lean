-- Prove2me | solution 1 for Aggmetrics.DataStream.eviction_entry_bound_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:27:36.833322+00:00
-- url     : https://prove2.me/submissions/a5f6edb9-619b-4ada-9c56-a60616bada57

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_antitone
import Theorems.Thm_Aggmetrics_DataStream_algState_sub_algStateE
import Theorems.Thm_Aggmetrics_DataStream_lost_entry
import Theorems.Thm_Aggmetrics_DataStream_abs_delta_le
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_nonneg


set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b|
      ≤ ((range n).filter (fun k => discarded α ε aud arr n k)).card * ε := by
  rw [algState_sub_algStateE α ε y yt p aud arr harr n, lost_entry]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k),
        |fadeWeight α n k * ((y k a - yt k a) * p k b)|
      ≤ ∑ k ∈ (range n).filter (fun k => discarded α ε aud arr n k), ε := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        obtain ⟨hkr, hd⟩ := Finset.mem_filter.mp hk
        obtain ⟨ha, harn, hne, hw⟩ := hd
        have hW0 : 0 ≤ fadeWeight α n k := fadeWeight_nonneg h0 h1.le n k
        have hWε : fadeWeight α n k < ε :=
          lt_of_le_of_lt (fadeWeight_antitone h0 h1.le (by omega : arr k - 1 ≤ n)) hw
        rw [abs_mul, abs_of_nonneg hW0]
        exact (mul_le_of_le_one_right hW0 (abs_delta_le y yt p hy hyt hp k a b)).trans hWε.le
    _ = ((range n).filter (fun k => discarded α ε aud arr n k)).card * ε := by
        rw [Finset.sum_const, nsmul_eq_mul]
end Aggmetrics.DataStream
