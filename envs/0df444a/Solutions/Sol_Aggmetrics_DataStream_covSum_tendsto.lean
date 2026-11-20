-- Prove2me | solution 1 for Aggmetrics.DataStream.covSum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:36:24.33587+00:00
-- url     : https://prove2.me/submissions/16351b5c-7225-41f9-b68a-1a4583bace86

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_covSum_bound

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α)
    (h1 : α < 1) :
    Tendsto (fun t => covSum ρ α t) atTop (𝓝 (kappaVar ρ α)) := by
  have hpow : Tendsto (fun t : ℕ => max 2 |kappaVar ρ α| * α ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).const_mul (max 2 |kappaVar ρ α|)
  have h : Tendsto (fun t => covSum ρ α t - kappaVar ρ α) atTop (𝓝 0) :=
    squeeze_zero_norm (fun t => by
      rw [Real.norm_eq_abs]
      exact covSum_bound hρ0 hρ h0 h1 t) hpow
  exact tendsto_sub_nhds_zero_iff.mp h
end Aggmetrics.DataStream
