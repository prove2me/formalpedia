-- Prove2me | solution 1 for Aggmetrics.DataStream.window_sizing_latency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:28:54.492518+00:00
-- url     : https://prove2.me/submissions/7a2ba6b0-47dd-4c4e-8f0a-acb960c82380

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
import Theorems.Thm_Aggmetrics_DataStream_window_sizing_rule


set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (pb δ : ℝ) (hp1 : 0 < pb) (hp2 : pb < 1) (hδ : 0 < δ)
    (Δ W : ℕ) (hΔ : Δ ≤ W)
    (hW : (W : ℝ) ≥ Δ + Real.log (1 / δ) / (-Real.log (1 - pb))) :
    (1 - pb) ^ (W - Δ) ≤ δ := by
  refine window_sizing_rule pb δ hp1 hp2 hδ (W - Δ) ?_
  rw [Nat.cast_sub hΔ]
  linarith
end Aggmetrics.DataStream
