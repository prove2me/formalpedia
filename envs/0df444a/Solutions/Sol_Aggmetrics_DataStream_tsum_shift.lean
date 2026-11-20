-- Prove2me | solution 1 for Aggmetrics.DataStream.tsum_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:57.026013+00:00
-- url     : https://prove2.me/submissions/2e985535-5aaf-40ee-bb2f-2d619f488050

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (ρ : ℕ → ℝ) (α : ℝ) :
    ∑' d : ℕ, α ^ (d + 1) * ρ (d + 1) = α * ∑' d : ℕ, α ^ d * ρ (d + 1) := by
  rw [← tsum_mul_left]
  exact tsum_congr (fun d => by ring)
end Aggmetrics.DataStream
