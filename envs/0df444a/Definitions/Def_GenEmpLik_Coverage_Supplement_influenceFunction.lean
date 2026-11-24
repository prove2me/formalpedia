-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_influenceFunction
-- name    : GenEmpLik_Coverage_Supplement_influenceFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:14:20.459314+00:00
-- url     : https://prove2.me/theorems/a0d5736f-350b-4902-a657-a022ebf76443
-- title:
--   Equation (25) — centered influence and canonical tangent set
-- statement:
--   For a probability law $P$, the derivative of a functional on the class $H$ has influence $\psi$ when $\psi$ is measurable and square-integrable under $P$, and
--   $$E_P\psi=0,\qquad dT(Q-P)=\int\psi\,d(Q-P)=E_Q\psi$$
--   for every probability law $Q$ in the functional domain, with the integrals defined. Its variance is required to be strictly positive in the coverage theorem. The canonical tangent set $B(H,P)$ consists of bounded signed-measure functionals uniformly continuous for
--   $$d_P(h_i,h_j)=\sqrt{E_P[(h_i-h_j)^2]}.$$
--   Theorem 10 allows any tangent set carrying the Gaussian limit; it does not force the canonical choice. Genuine integrability under each law in (25) is included, preventing Lean's default value for undefined Bochner integrals.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 23, (25) and following paragraph

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_functionalDomain

open MeasureTheory
open scoped ENNReal

namespace GenEmpLik.Coverage.Supplement

/-- Equation (25), p. 23: a centered, square-integrable canonical influence,
with genuine integrals for every probability measure in the functional domain. -/
def IsInfluence {Ξ ι : Type*} [MeasurableSpace Ξ]
    (h : ι → Ξ → ℝ) (P : Measure Ξ) (dT : ProcessSpace ι → ℝ)
    (ψ : Ξ → ℝ) : Prop :=
  Measurable ψ ∧ Integrable (fun z => ψ z ^ 2) P ∧ (∫ z, ψ z ∂P) = 0 ∧
  ∀ Q : Measure Ξ, IsProbabilityMeasure Q →
    (∀ i, Integrable (h i) Q) → Memℓp (fun i => ∫ z, h i z ∂Q) ∞ →
    Integrable ψ Q ∧ dT (measureProcess h Q - measureProcess h P) = ∫ z, ψ z ∂Q

/-- The canonical tangent set B(H,P) described after (25): signed-measure
functionals uniformly continuous for the L²(P) semimetric. Theorem 10 permits
any tangent set carrying its Gaussian limit, not only this canonical choice. -/
def canonicalTangent {Ξ ι : Type*} [MeasurableSpace Ξ]
    (h : ι → Ξ → ℝ) (P : Measure Ξ) : Set (ProcessSpace ι) :=
  {v | v ∈ signedDomain h ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ i j, Real.sqrt (∫ z, (h i z - h j z) ^ 2 ∂P) < δ → |v i - v j| < ε}

end GenEmpLik.Coverage.Supplement


