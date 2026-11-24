-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:26.082579+00:00
-- url     : https://prove2.me/theorems/72f06c31-eb2c-441a-b75c-c1976d1de930
-- title:
--   Schwartz Eq Zero Of Wrong Sign Gaussian Relation
-- statement:
--   Definitions and structural lemmas for Schwartz Eq Zero Of Wrong Sign Gaussian Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzEqZeroOfWrongSignGaussianRelation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
namespace GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
def sesq : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℝ ℂ).flip.comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).flip
def mulForm (ℓ : V →ₗ[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (⇑(LinearMap.toContinuousLinearMap ℓ))
def twD (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f - (2 * Real.pi * Complex.I) • mulForm ℓ f
section integrals
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
def ip (u w : 𝓢(V, ℂ)) : ℂ := ∫ x, u x * conj (w x) ∂μ
end integrals
section main
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
end main
end GlobalTheory.WrongSignGauss


