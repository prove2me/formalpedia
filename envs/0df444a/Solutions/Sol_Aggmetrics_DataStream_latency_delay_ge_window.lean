-- Prove2me | solution 1 for Aggmetrics.DataStream.latency_delay_ge_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:52.757046+00:00
-- url     : https://prove2.me/submissions/25c8626b-e4bb-4fdf-b996-100224f69390

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (pb : ℝ) (Δ W : ℕ) (hΔ : W ≤ Δ) :
    ∏ s ∈ range W, (1 - pb * (if Δ ≤ s then (1 : ℝ) else 0)) = 1 := by
  refine Finset.prod_eq_one (fun s hs => ?_)
  have : s < W := Finset.mem_range.mp hs
  have : ¬ Δ ≤ s := by omega
  simp [this]
end Aggmetrics.DataStream
