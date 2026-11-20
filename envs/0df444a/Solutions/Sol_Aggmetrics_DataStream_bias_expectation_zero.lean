-- Prove2me | solution 1 for Aggmetrics.DataStream.bias_expectation_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:18:00.801861+00:00
-- url     : https://prove2.me/submissions/7015a155-a6f0-4189-a88f-68cd6e263aba

import Definitions.Def_Aggmetrics_DataStreamTemporal
import Definitions.Def_Aggmetrics_DataStreamDelay

set_option autoImplicit true
open Finset Matrix MeasureTheory
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m n : ℕ}
    (w O : Fin n → ℝ) (p : Fin n → Fin m → ℝ) (y yt : Fin n → Ω → Fin m → ℝ)
    (hint : ∀ k a, Integrable (fun ω => y k ω a - yt k ω a) μ)
    (hcal : ∀ k a, ∫ ω, (y k ω a - yt k ω a) ∂μ = 0) (a b : Fin m) :
    ∫ ω, (∑ k, ((1 - O k) * w k) • outer (fun c => y k ω c - yt k ω c) (p k)) a b ∂μ = 0 := by
  have h : ∀ ω, (∑ k, ((1 - O k) * w k) • outer (fun c => y k ω c - yt k ω c) (p k)) a b
      = ∑ k, ((1 - O k) * w k * p k b) * (y k ω a - yt k ω a) := by
    intro ω
    simp only [Matrix.sum_apply, Matrix.smul_apply, outer, Matrix.of_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp_rw [h]
  rw [integral_finset_sum _ (fun k _ => (hint k a).const_mul _)]
  simp [integral_const_mul, hcal]
end Aggmetrics.DataStream
