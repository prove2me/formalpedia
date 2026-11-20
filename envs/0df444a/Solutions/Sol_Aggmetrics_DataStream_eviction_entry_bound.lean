-- Prove2me | solution 1 for Aggmetrics.DataStream.eviction_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:04.70771+00:00
-- url     : https://prove2.me/submissions/f83e5b1e-d7b2-438e-a8a1-127adbbfd197

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamEviction
import Theorems.Thm_Aggmetrics_DataStream_algState_sub_algStateE
import Theorems.Thm_Aggmetrics_DataStream_evicted_sum_bound
import Theorems.Thm_Aggmetrics_DataStream_lost_entry
import Theorems.Thm_Aggmetrics_DataStream_abs_delta_le

set_option autoImplicit true
open Finset Matrix
open scoped Classical
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {m : ℕ} (α ε : ℝ) (y yt p : ℕ → Fin m → ℝ) (aud : ℕ → Prop)
    (arr : ℕ → ℕ) (harr : ∀ k, k < arr k) (h0 : 0 ≤ α) (h1 : α < 1)
    (hy : ∀ k a, 0 ≤ y k a ∧ y k a ≤ 1) (hyt : ∀ k a, 0 ≤ yt k a ∧ yt k a ≤ 1)
    (hp : ∀ k a, 0 ≤ p k a ∧ p k a ≤ 1)
    {s : ℕ} (hs : ∀ j, (1 - α) * α ^ j < ε → s ≤ j) (n : ℕ) (a b : Fin m) :
    |(algState α y yt p aud arr n - algStateE α ε y yt p aud arr n) a b| ≤ α ^ s := by
  rw [algState_sub_algStateE α ε y yt p aud arr harr n, lost_entry]
  refine evicted_sum_bound h0 h1 n s _ ?_ (fun k => (y k a - yt k a) * p k b)
    (fun k => abs_delta_le y yt p hy hyt hp k a b)
  intro k hk
  obtain ⟨hkr, hd⟩ := Finset.mem_filter.mp hk
  refine ⟨Finset.mem_range.mp hkr, ?_⟩
  obtain ⟨ha, harn, hne, hw⟩ := hd
  have hakk := harr k
  have hj : (1 - α) * α ^ (arr k - 1 - 1 - k) < ε := by
    have e : fadeWeight α (arr k - 1) k = (1 - α) * α ^ (arr k - 1 - 1 - k) := rfl
    rw [← e]
    exact hw
  have := hs _ hj
  omega
end Aggmetrics.DataStream
