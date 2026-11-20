-- Prove2me | solution 1 for Aggmetrics.DataStream.fading_variance_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:37:48.965193+00:00
-- url     : https://prove2.me/submissions/1b2befa8-918b-4e5b-a258-be537d8bda0b

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr
import Theorems.Thm_Aggmetrics_DataStream_fading_variance_autocorr
import Theorems.Thm_Aggmetrics_DataStream_covSum_tendsto

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j)))
    (hρ0 : ρ 0 = 1) (hρ : ∀ d, |ρ d| ≤ 1) {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    Tendsto (fun t => Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]) atTop
      (𝓝 (v * kappaVar ρ α)) := by
  have := (covSum_tendsto hρ0 hρ h0 h1).const_mul v
  refine this.congr (fun t => ?_)
  rw [fading_variance_autocorr μ X hL2 v ρ hcov α t]
end Aggmetrics.DataStream
