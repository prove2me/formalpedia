-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_LpTop
-- name    : MarkovProcessModule_MarkovProcess_Kernel_LpTop
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T19:41:02.861436+00:00
-- url     : https://prove2.me/theorems/d8f3ef8f-cf86-460f-be12-097c45f3646d
-- title:
--   MarkovProcess.Kernel.LpTop
-- statement:
--   # The kernel integral on `L^∞`
--
--   This file proves the real-valued `L^∞` contraction estimate for integration
--   against a sub-Markov kernel preserving a subinvariant measure.  The operator
--   itself is packaged as a continuous linear map by `kernelLpTop` in
--   `Kernel/Lp.lean`.
--
--   Complete pinned Lean module MarkovProcess.Kernel.LpTop by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Kernel/LpTop.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Kernel_Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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


