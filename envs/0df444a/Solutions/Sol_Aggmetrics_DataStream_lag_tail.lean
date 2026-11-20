-- Prove2me | solution 1 for Aggmetrics.DataStream.lag_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:10.398224+00:00
-- url     : https://prove2.me/submissions/6370ffe1-f727-4bf7-8454-7a169ba8f32f

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_hasSum_fade_geom
import Theorems.Thm_Aggmetrics_DataStream_summable_lag

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    |lagSum ρ α t - einf ρ α| ≤ α ^ t := by
  have hs := summable_lag hρ h0 h1
  have hsplit : (∑ d ∈ range t, (1 - α) * α ^ d * ρ (d + 1))
      + ∑' i : ℕ, (1 - α) * α ^ (i + t) * ρ (i + t + 1)
      = ∑' d : ℕ, (1 - α) * α ^ d * ρ (d + 1) := hs.sum_add_tsum_nat_add t
  have h : lagSum ρ α t - einf ρ α
      = -∑' i : ℕ, (1 - α) * α ^ (i + t) * ρ (i + t + 1) := by
    unfold lagSum einf
    linarith
  rw [h, abs_neg]
  have := tsum_of_norm_bounded (hasSum_fade_geom h0 h1 t)
    (f := fun i : ℕ => (1 - α) * α ^ (i + t) * ρ (i + t + 1)) (fun i => by
      have h2 : 0 ≤ (1 - α) * α ^ (i + t) := mul_nonneg (by linarith) (pow_nonneg h0 _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
      exact mul_le_of_le_one_right h2 (hρ _))
  simpa [Real.norm_eq_abs] using this
end Aggmetrics.DataStream
