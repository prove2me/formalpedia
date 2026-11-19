-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CharTotal_F000
-- name    : LevyStochCalc_Probability_CharTotal_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:01:09.225755+00:00
-- url     : https://prove2.me/theorems/d8a5741c-c2b7-467c-83fa-11c11e5f844c
-- title:
--   Source declarations: LevyStochCalc.Probability.CharTotal
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Probability.CharTotal, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Characters separate `L¹` densities

An integrable function on an inner-product space that integrates to zero against every character
`v ↦ exp(i⟪v, w⟫)` vanishes almost everywhere. Splitting the function into positive and negative
parts turns the hypothesis into an equality of the characteristic functions of two finite
measures, which `MeasureTheory.Measure.ext_of_charFun` reads as an equality of the measures.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]

omit [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] in
/-- The characteristic function of a density-weighted measure. -/
theorem charFun_withDensity_ofReal {μ : Measure V} {u : V → ℝ} (hu : AEMeasurable u μ) (w : V) :
    charFun (μ.withDensity fun v => ENNReal.ofReal (u v)) w
      = ∫ v, Real.toNNReal (u v) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ := by
  rw [charFun_apply]
  exact integral_withDensity_eq_integral_smul₀ (f := fun v => Real.toNNReal (u v))
    hu.real_toNNReal _
omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A character is bounded and continuous, so it multiplies an integrable function into an
integrable one. -/
theorem integrable_char_smul {μ : Measure V} {z : V → ℝ} (hz : Integrable z μ) (w : V) :
    Integrable (fun v => z v • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)) μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine Integrable.mono' hz.norm
    (hz.aestronglyMeasurable.smul hcont.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]
omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A character multiplies an integrable complex function into an integrable one. -/
theorem integrable_char_mul {μ : Measure V} {g : V → ℂ} (hg : Integrable g μ) (w : V) :
    Integrable (fun v => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v) μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine Integrable.mono' hg.norm
    (hcont.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]
omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A character composed with a measurable map multiplies an integrable function into an
integrable one. -/
theorem integrable_charComp_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → V}
    (hX : Measurable X) {z : Ω → ℝ} (hz : Integrable z P) (w : V) :
    Integrable (fun ω => z ω • Complex.exp ((⟪X ω, w⟫ : ℝ) * Complex.I)) P := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine Integrable.mono' hz.norm
    (hz.aestronglyMeasurable.smul (hcont.measurable.comp hX).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]
/-- The complex conjugate of an integrable function is integrable. -/
theorem integrable_conj {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ}
    (hg : Integrable g μ) :
    Integrable (fun v => (starRingEnd ℂ) (g v)) μ := by
  refine Integrable.mono' hg.norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp
/-- The positive part of an integrable function is integrable. -/
theorem integrable_toNNReal_coe {α : Type*} [MeasurableSpace α] {μ : Measure α} {z : α → ℝ}
    (hz : Integrable z μ) :
    Integrable (fun v => ((Real.toNNReal (z v) : ℝ≥0) : ℝ)) μ := by
  refine Integrable.mono' hz.norm
    (hz.aemeasurable.real_toNNReal.coe_nnreal_real).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.norm_eq_abs, Real.coe_toNNReal']
  rcases le_total 0 (z v) with hv | hv
  · rw [max_eq_left hv, abs_of_nonneg hv]
  · rw [max_eq_right hv]
    simp
/-! ### Totality in `L²` -/

/-! ### Transfer along a random vector -/

/-! ### Set integrals over the σ-algebra generated by a random vector

The transfer lemma above needs `Z` to be measurable for `σ(X)`. When it is not — the case the
predictable representation property meets, where `Z` is measurable for a much larger σ-algebra —
the characters still say something: the complex measure `Z dP` pushed forward by `X` has
vanishing Fourier transform, so `Z` integrates to zero over every set `X` generates.
-/

section Comap

variable {Ω : Type*} [MeasurableSpace Ω]

end Comap

/-! ### Real and imaginary parts against a unimodular conjugation-closed family -/

/-! ### Vanishing set integrals over what a random vector generates -/

section SetIntegral

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

end SetIntegral

end LevyStochCalc.Probability


