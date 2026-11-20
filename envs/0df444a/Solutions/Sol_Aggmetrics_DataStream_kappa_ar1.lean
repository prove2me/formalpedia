-- Prove2me | solution 1 for Aggmetrics.DataStream.kappa_ar1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:33:15.487176+00:00
-- url     : https://prove2.me/submissions/50665698-63dc-4c3e-89c5-86a70e7be127

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {α r : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hr : |r| < 1) :
    kappaFactor (fun d => r ^ d) α = (1 + α * r) / (1 - α * r) := by
  have habs : |α * r| < 1 := by
    rw [abs_mul, abs_of_nonneg h0]
    nlinarith [abs_nonneg r]
  have hne : 1 - α * r ≠ 0 := by
    have := (abs_lt.mp habs).2
    linarith
  unfold kappaFactor
  show 1 + 2 * ∑' d : ℕ, α ^ (d + 1) * r ^ (d + 1) = _
  have h : ∑' d : ℕ, α ^ (d + 1) * r ^ (d + 1) = (α * r) / (1 - α * r) := by
    have e : ∀ d : ℕ, α ^ (d + 1) * r ^ (d + 1) = (α * r) * (α * r) ^ d := fun d => by
      rw [← mul_pow, pow_succ]
      ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_abs_lt_one habs, ← div_eq_mul_inv]
  rw [h]
  field_simp
  ring
end Aggmetrics.DataStream
