-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_functionalDomain
-- name    : GenEmpLik_Coverage_Supplement_functionalDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:12:25.640558+00:00
-- url     : https://prove2.me/theorems/1763e8b5-9e5d-4ac7-a860-d9c2101e5d55
-- title:
--   Probability and signed-measure functional domains and confidence image
-- statement:
--   For an arbitrary measurable class $H=\{h_i\}$, let $\mathcal M$ be the restrictions to $H$ of finite signed measures whose integrals are defined and uniformly bounded, and let $\mathcal P$ be the corresponding probability-measure restrictions. Both are realized in the uniform-norm space $\ell^\infty(H)$, identifying measures with the same action on $H$. Signed integration is positive-Jordan-part integration minus negative-Jordan-part integration. For a real functional $T:\mathcal P\to\mathbb R$, define
--   $$C_{n,\rho}(T)=\left\{T\!\left(\sum_jp_j\delta_{z_j}\right):p\in\mathcal P_{n,\rho}\right\}.$$
--   This is the actual image used in general functional coverage, rather than an interval defined only by its endpoints.
--
--   **Formalization Note** Every class function is required to be integrable under both Jordan parts, or under the represented probability law. The population and functional domain remain general, while feasible confidence-image laws are absolutely continuous with respect to the empirical law. This module does not use the specialized optimal-value confidence set.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 22, Section 7.2; 23, (26)

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_empiricalProcess
import Definitions.Def_GenEmpLik_Coverage_divergenceBall

open MeasureTheory

namespace GenEmpLik.Coverage.Supplement

/-- Signed measures bounded on H, realized in the uniform-norm space, p. 22.
Integrability on both Jordan parts makes signed integration genuine. -/
def signedDomain {Ξ ι : Type*} [MeasurableSpace Ξ]
    (h : ι → Ξ → ℝ) : Set (ProcessSpace ι) :=
  {v | ∃ s : SignedMeasure Ξ, ∀ i,
    Integrable (h i) s.toJordanDecomposition.posPart ∧
    Integrable (h i) s.toJordanDecomposition.negPart ∧
    v i = (∫ z, h i z ∂s.toJordanDecomposition.posPart) -
      (∫ z, h i z ∂s.toJordanDecomposition.negPart)}

/-- All probability measures bounded on H, identified by their action on H, p. 22.
No finite, parametric or dominated restriction is imposed. -/
def probabilityDomain {Ξ ι : Type*} [MeasurableSpace Ξ]
    (h : ι → Ξ → ℝ) : Set (ProcessSpace ι) :=
  {v | ∃ Q : Measure Ξ, IsProbabilityMeasure Q ∧
    ∀ i, Integrable (h i) Q ∧ v i = ∫ z, h i z ∂Q}

/-- The general functional image C_{n,rho}, (26), p. 23.
This uses T itself, not the optimal-value specialization. -/
noncomputable def functionalImage {Ξ ι : Type*} {n : ℕ}
    (h : ι → Ξ → ℝ) (T : ProcessSpace ι → ℝ)
    (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → Ξ) : Set ℝ :=
  (fun p => T (weightedProcess h z p)) '' GenEmpLik.Coverage.divergenceBall f ρ n

end GenEmpLik.Coverage.Supplement


