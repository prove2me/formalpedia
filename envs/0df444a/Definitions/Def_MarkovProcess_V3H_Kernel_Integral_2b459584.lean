-- Prove2me | Definitions.Def_MarkovProcess_V3H_Kernel_Integral_2b459584
-- name    : MarkovProcess_V3H_Kernel_Integral_2b459584
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:27:46.390912+00:00
-- url     : https://prove2.me/theorems/6e1cf49a-51bd-46ab-8800-abe9993de466
-- title:
--   MarkovProcess: MarkovProcess_V3H_Kernel_Integral_2b459584
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Integration against a kernel

This file defines the raw real-valued integral operator associated with a
kernel.  Subinvariance of a measure makes this operator independent, almost
everywhere, of the chosen representative of its input.
-/

open MeasureTheory
open ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

/-- The raw real-valued integral of `f` against the measure `κ x`. -/
noncomputable def kernelIntegral (κ : Kernel α α) (f : α → ℝ) (x : α) : ℝ :=
  ∫ y, f y ∂κ x

/-- Subinvariance transports an almost-everywhere statement for `μ` to the
kernel measures `κ x`, for almost every `x` with respect to `μ`. -/
theorem ae_ae_kernel_of_comp_le {μ : Measure α} {κ : Kernel α α} {p : α → Prop}
    (hκμ : κ ∘ₘ μ ≤ μ) (hp : ∀ᵐ y ∂μ, p y) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, p y := by
  apply Measure.ae_ae_of_ae_comp
  exact Measure.ae_le_iff_absolutelyContinuous.mpr
    (Measure.absolutelyContinuous_of_le hκμ) hp

/-- Under subinvariance, the raw kernel integral depends only on the
`μ`-almost-everywhere equivalence class of its input. -/
theorem kernelIntegral_congr_ae {μ : Measure α} {κ : Kernel α α} {f g : α → ℝ}
    (hκμ : κ ∘ₘ μ ≤ μ) (hfg : f =ᵐ[μ] g) :
    kernelIntegral κ f =ᵐ[μ] kernelIntegral κ g := by
  filter_upwards [ae_ae_kernel_of_comp_le hκμ hfg] with x hx
  exact integral_congr_ae hx

/-- Under subinvariance, integrating an almost-everywhere strongly measurable
function against `κ x` gives an almost-everywhere strongly measurable function
of `x`. -/
theorem AEStronglyMeasurable.kernelIntegral {μ : Measure α} {κ : Kernel α α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f μ) (hκμ : κ ∘ₘ μ ≤ μ) :
    AEStronglyMeasurable (kernelIntegral κ f) μ := by
  let hfComp : AEStronglyMeasurable f (κ ∘ₘ μ) :=
    hf.mono_ac (Measure.absolutelyContinuous_of_le hκμ)
  refine ⟨fun x ↦ MarkovProcess.kernelIntegral κ (hfComp.mk f) x, ?_, ?_⟩
  · exact hfComp.stronglyMeasurable_mk.integral_kernel
  · filter_upwards [Measure.ae_ae_of_ae_comp hfComp.ae_eq_mk] with x hx
    exact integral_congr_ae hx

end MarkovProcess


