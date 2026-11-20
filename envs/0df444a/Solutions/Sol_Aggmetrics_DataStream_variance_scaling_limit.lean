-- Prove2me | solution 1 for Aggmetrics.DataStream.variance_scaling_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:03:05.12268+00:00
-- url     : https://prove2.me/submissions/07fc2a01-2dfd-44a1-872c-a79e5a74cfe3

import Definitions.Def_Aggmetrics_Basic
import Definitions.Def_Aggmetrics_DataStream

set_option autoImplicit true
open Finset MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (α v : ℝ) (hα1 : 0 < α) (hα2 : α < 1) :
    Filter.Tendsto (fun t : ℕ => (1 - α) ^ 2 * (∑ k ∈ Finset.range t, α ^ (2 * k)) * v)
      Filter.atTop (nhds ((1 - α) / (1 + α) * v)) := by
  have hα2_nonneg : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hα2_lt_one : α ^ 2 < 1 := by nlinarith
  have hsum : HasSum (fun k : ℕ => (α ^ 2) ^ k) (1 - α ^ 2)⁻¹ :=
    hasSum_geometric_of_lt_one hα2_nonneg hα2_lt_one
  have htendsto :
      Filter.Tendsto (fun t : ℕ => ∑ k ∈ Finset.range t, (α ^ 2) ^ k) Filter.atTop
        (nhds (1 - α ^ 2)⁻¹) :=
    hsum.tendsto_sum_nat
  have heq : ∀ t : ℕ, (∑ k ∈ Finset.range t, α ^ (2 * k)) = ∑ k ∈ Finset.range t, (α ^ 2) ^ k := by
    intro t
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_mul]
  have hfinal :
      Filter.Tendsto (fun t : ℕ => (1 - α) ^ 2 * (∑ k ∈ Finset.range t, (α ^ 2) ^ k) * v)
        Filter.atTop (nhds ((1 - α) ^ 2 * (1 - α ^ 2)⁻¹ * v)) :=
    (htendsto.const_mul ((1 - α) ^ 2)).mul_const v
  have h1pα : (1 : ℝ) + α ≠ 0 := by linarith
  have h1mα : (1 : ℝ) - α ≠ 0 := by linarith
  have hval : (1 - α) ^ 2 * (1 - α ^ 2)⁻¹ * v = (1 - α) / (1 + α) * v := by
    have h1ma2 : (1 : ℝ) - α ^ 2 ≠ 0 := by
      have : (1 : ℝ) - α ^ 2 = (1 - α) * (1 + α) := by ring
      rw [this]; exact mul_ne_zero h1mα h1pα
    field_simp
    ring
  simpa only [heq, hval] using hfinal
end Aggmetrics.DataStream
