-- Prove2me | solution 1 for Aggmetrics.DataStream.fading_variance_autocorr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:30:48.954468+00:00
-- url     : https://prove2.me/submissions/7a03ec50-7d1a-4ae7-b719-2dac07104097

import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamAutocorr

set_option autoImplicit true
open Finset ProbabilityTheory MeasureTheory Filter Topology
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (ρ : ℕ → ℝ)
    (hcov : ∀ i j, cov[X i, X j; μ] = v * ρ (Int.natAbs ((i : ℤ) - j))) (α : ℝ) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ] = v * covSum ρ α t := by
  rw [variance_fun_sum' (fun k _ => (hL2 k).const_mul (fadeWeight α t k))]
  unfold covSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  ring
end Aggmetrics.DataStream
