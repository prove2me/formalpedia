-- Prove2me | solution 1 for Aggmetrics.DataStream.einf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:55.344669+00:00
-- url     : https://prove2.me/submissions/ef1fdf6f-2b20-4087-a1b0-c9a17586923a

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (ρ : ℕ → ℝ) (α : ℝ) :
    einf ρ α = (1 - α) * ∑' d : ℕ, α ^ d * ρ (d + 1) := by
  unfold einf
  rw [← tsum_mul_left]
  exact tsum_congr (fun d => by ring)
end Aggmetrics.DataStream
