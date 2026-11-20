-- Prove2me | solution 1 for Aggmetrics.DataStream.latency_const_delay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:41.842543+00:00
-- url     : https://prove2.me/submissions/6aadc219-29b2-463c-b686-1beafa8bb820

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (pb : ℝ) (Δ W : ℕ) (hΔ : Δ ≤ W) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = (1 - pb) ^ (W - Δ) := by
  have h := Finset.prod_Ico_consecutive
    (fun s => 1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) (Nat.zero_le Δ) hΔ
  rw [Finset.range_eq_Ico, ← h]
  have h1 : ∏ s ∈ Ico 0 Δ, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 := by
    refine Finset.prod_eq_one (fun s hs => ?_)
    have : s < Δ := (Finset.mem_Ico.mp hs).2
    simp [not_le.mpr this]
  have h2 : ∏ s ∈ Ico Δ W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = (1 - pb) ^ (W - Δ) := by
    rw [Finset.prod_congr rfl (fun s hs => by
      have : Δ ≤ s := (Finset.mem_Ico.mp hs).1
      simp [this] : ∀ s ∈ Ico Δ W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 - pb)]
    rw [Finset.prod_const, Nat.card_Ico]
  rw [h1, h2, one_mul]
end Aggmetrics.DataStream
