-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_LpTop_7ab9dc29
-- name    : MarkovProcess_V3H_Kernel_LpTop_7ab9dc29
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:17.882132+00:00
-- url     : https://prove2.me/theorems/d2aa5886-8e03-4892-b943-9c35fe2b752f
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_LpTop_7ab9dc29
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The kernel integral on `L^∞`

This file proves the real-valued `L^∞` contraction estimate for integration
against a sub-Markov kernel preserving a subinvariant measure.  The operator
itself is packaged as a continuous linear map by `kernelLpTop` in
`Kernel/Lp.lean`.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- Integrating a function bounded almost everywhere by `C` against a
sub-Markov kernel measure preserves that bound. -/
theorem enorm_kernelIntegral_le_of_ae {κ : ProbabilityTheory.Kernel α α}
    (hκ : IsSubMarkovKernel κ) {f : α → ℝ} {C : ℝ≥0∞} {x : α}
    (hf : ∀ᵐ y ∂κ x, ‖f y‖ₑ ≤ C) :
    ‖kernelIntegral κ f x‖ₑ ≤ C := by
  calc
    ‖kernelIntegral κ f x‖ₑ ≤ ∫⁻ y, ‖f y‖ₑ ∂κ x :=
      enorm_integral_le_lintegral_enorm f
    _ ≤ ∫⁻ _y, C ∂κ x := lintegral_mono_ae hf
    _ = C * κ x Set.univ := lintegral_const C
    _ ≤ C * 1 := mul_le_mul_right (hκ.measure_le_one x Set.univ) C
    _ = C := mul_one C

/-- The essential-supremum bound for `f` bounds its kernel integral almost
everywhere under subinvariance. -/
theorem enorm_kernelIntegral_ae_le_eLpNormEssSup {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (f : α → ℝ) :
    ∀ᵐ x ∂μ, ‖kernelIntegral κ f x‖ₑ ≤ eLpNormEssSup f μ := by
  filter_upwards
    [ae_ae_kernel_of_comp_le hκμ (enorm_ae_le_eLpNormEssSup f μ)] with x hx
  exact enorm_kernelIntegral_le_of_ae hκ hx

/-- Integration against a sub-Markov kernel is a contraction for the raw
`L^∞` seminorm under subinvariance. -/
theorem eLpNorm_kernelIntegral_top_le {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (f : α → ℝ) :
    eLpNorm (kernelIntegral κ f) ∞ μ ≤ eLpNorm f ∞ μ := by
  rw [eLpNorm_exponent_top, eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_enorm_bound
    (enorm_kernelIntegral_ae_le_eLpNormEssSup hκ hκμ f)

/-- Integration against a sub-Markov kernel sends `L^∞` functions to
`L^∞` functions under subinvariance. -/
theorem MemLp.kernelIntegral_top {μ : Measure α}
    {κ : ProbabilityTheory.Kernel α α} (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) {f : α → ℝ} (hf : MemLp f ∞ μ) :
    MemLp (kernelIntegral κ f) ∞ μ := by
  refine ⟨AEStronglyMeasurable.kernelIntegral hf.aestronglyMeasurable hκμ, ?_⟩
  exact (eLpNorm_kernelIntegral_top_le hκ hκμ f).trans_lt hf.2

end MarkovProcess


