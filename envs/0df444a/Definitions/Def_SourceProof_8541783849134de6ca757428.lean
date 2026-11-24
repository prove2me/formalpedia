-- Prove2me | Definitions.Def_SourceProof_8541783849134de6ca757428
-- name    : SourceProof_8541783849134de6ca757428
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:59.656277+00:00
-- url     : https://prove2.me/theorems/fa3f0e8a-92c2-453d-8214-af7e8cca9620
-- title:
--   StochLean source theorem: StochLean.measurable_lintegral_kernel_of_finite_fibers

import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jointly measurable lower integrals with locally finite random measures

The finite-fiber argument uses Mathlib's measurable sections theorem and simple
function approximation. No uniform bound on the random total masses is needed.
An increasing finite-measure exhaustion then gives the half-line result.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8541783849134de6ca757428
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {κ : Kernel Ω T}
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {f : Ω × T → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun ω ↦ ∫⁻ t, f (ω, t) ∂κ ω := by
  let S : ℕ → SimpleFunc (Ω × T) ℝ≥0∞ := SimpleFunc.eapprox f
  have heq (ω : Ω) : (∫⁻ t, f (ω, t) ∂κ ω) = ⨆ n, ∫⁻ t, S n (ω, t) ∂κ ω := by
    conv_lhs => arg 2; ext t; rw [← SimpleFunc.iSup_eapprox_apply hf (ω, t)]
    exact lintegral_iSup (fun n ↦ (S n).measurable.comp measurable_prodMk_left)
      (fun i j hij t ↦ SimpleFunc.monotone_eapprox f hij (ω, t))
  simp_rw [heq]
  refine Measurable.iSup fun n ↦ ?_
  refine SimpleFunc.induction
    (motive := fun s ↦ Measurable fun ω ↦ ∫⁻ t, s (ω, t) ∂κ ω) ?_ ?_ (S n)
  · intro c s hs
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    change Measurable fun ω ↦ ∫⁻ t, s.indicator (Function.const (Ω × T) c) (ω, t) ∂κ ω
    have heq (ω : Ω) : (∫⁻ t, s.indicator (Function.const (Ω × T) c) (ω, t) ∂κ ω) =
        c * κ ω (Prod.mk ω ⁻¹' s) :=
      lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hs c
    simp_rw [heq]
    exact (Kernel.measurable_kernel_prodMk_left_of_finite hs hκ).const_mul c
  · intro s t _ hs ht
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have heq : (fun ω ↦ ∫⁻ u, s (ω, u) + t (ω, u) ∂κ ω) =
        (fun ω ↦ ∫⁻ u, s (ω, u) ∂κ ω) + fun ω ↦ ∫⁻ u, t (ω, u) ∂κ ω := by
      funext ω
      exact lintegral_add_left ((s.measurable).comp measurable_prodMk_left) _
    rw [heq]
    exact hs.add ht
end StochLean


