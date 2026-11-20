-- Prove2me | solution 1 for Aggmetrics.DataStream.summable_lag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:40.633541+00:00
-- url     : https://prove2.me/submissions/dae9098a-860a-41fe-8140-98aa4f31f840

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_hasSum_fade_geom

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {ρ : ℕ → ℝ} (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Summable (fun d : ℕ => (1 - α) * α ^ d * ρ (d + 1)) := by
  have hg := hasSum_fade_geom h0 h1 0
  have hg' : HasSum (fun d : ℕ => (1 - α) * α ^ d) 1 := by simpa using hg
  have hb : ∀ d : ℕ, ‖(1 - α) * α ^ d * ρ (d + 1)‖ ≤ (1 - α) * α ^ d := fun d => by
    have h2 : 0 ≤ (1 - α) * α ^ d := mul_nonneg (by linarith) (pow_nonneg h0 d)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    exact mul_le_of_le_one_right h2 (hρ (d + 1))
  first
    | exact Summable.of_norm_bounded hg'.summable hb
    | exact Summable.of_norm_bounded _ hg'.summable hb
end Aggmetrics.DataStream
