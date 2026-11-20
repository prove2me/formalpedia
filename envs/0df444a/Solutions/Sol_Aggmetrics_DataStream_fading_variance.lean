-- Prove2me | solution 1 for Aggmetrics.DataStream.fading_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:32:04.619759+00:00
-- url     : https://prove2.me/submissions/b35bec78-78eb-471f-a0d1-c551954b9255

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift
import Theorems.Thm_Aggmetrics_DataStream_fadeWeight_sq_sum

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ)
    (hL2 : ∀ k, MemLp (X k) 2 μ) (v : ℝ) (hvar : ∀ k, Var[X k; μ] = v)
    {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (t : ℕ) :
    Var[fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω; μ]
      = (1 - α) / (1 + α) * (1 - α ^ (2 * t)) * v := by
  have hsum : (fun ω => ∑ k ∈ range t, fadeWeight α t k * X k ω)
      = ∑ k ∈ range t, (fun ω => fadeWeight α t k * X k ω) := by
    ext ω
    simp [Finset.sum_apply]
  have hcomp : iIndepFun (fun k => (fun x : ℝ => fadeWeight α t k * x) ∘ X k) μ :=
    hX.comp (fun k x => fadeWeight α t k * x) (fun k => measurable_const.mul measurable_id)
  rw [hsum, IndepFun.variance_sum (fun k _ => (hL2 k).const_mul (fadeWeight α t k))
    (fun i _ j _ hij => hcomp.indepFun hij)]
  have hk : ∀ k ∈ range t, Var[fun ω => fadeWeight α t k * X k ω; μ]
      = (fadeWeight α t k) ^ 2 * v := fun k _ => by
    rw [variance_const_mul, hvar k]
  rw [Finset.sum_congr rfl hk, ← Finset.sum_mul, fadeWeight_sq_sum h0 h1]
end Aggmetrics.DataStream
