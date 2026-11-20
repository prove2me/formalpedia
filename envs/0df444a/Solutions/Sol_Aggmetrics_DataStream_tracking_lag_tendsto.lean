-- Prove2me | solution 1 for Aggmetrics.DataStream.tracking_lag_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:54.230775+00:00
-- url     : https://prove2.me/submissions/63ba3796-1847-47a8-842e-c64f0199b2a3

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_tracking_lag

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α a d : ℝ) (h0 : 0 ≤ α) (h1 : α < 1) (c : ℕ → ℝ)
    (hc : ∀ n, c (n + 1) = α * c n + (1 - α) * (a + (n + 1 : ℕ) * d)) :
    Tendsto (fun n : ℕ => c n - (a + n * d)) atTop (nhds (-(α * d) / (1 - α))) := by
  have hpow : Tendsto (fun n : ℕ => α ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have h := (hpow.mul_const (c 0 - a + α * d / (1 - α))).const_add (-(α * d) / (1 - α))
  simp only [zero_mul, add_zero] at h
  refine h.congr (fun n => ?_)
  rw [tracking_lag α a d h1 c hc n]
end Aggmetrics.DataStream
