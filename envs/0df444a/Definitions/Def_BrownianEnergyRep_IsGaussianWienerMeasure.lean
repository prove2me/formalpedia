-- Prove2me | Definitions.Def_BrownianEnergyRep_IsGaussianWienerMeasure
-- name    : BrownianEnergyRep_IsGaussianWienerMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:36.53266+00:00
-- url     : https://prove2.me/theorems/4deaf46e-363d-4322-ad97-c07f3e09c972
-- title:
--   The Wiener measure $\nu$ on $W(\mathfrak g)$
-- statement:
--   $\nu$ is the law of the standard $\mathfrak g$-valued Brownian motion with covariance determined by $\langle\cdot,\cdot\rangle$: a centred Gaussian measure on $W(\mathfrak g)$ with
--   $$
--   \operatorname{Cov}\big(\langle a,w_s\rangle,\langle b,w_t\rangle\big)=\langle a,b\rangle\min(s,t),\qquad a,b\in\mathfrak g,\ s,t\in[0,T].
--   $$
--
--   **Formalization Note** The paper names $\nu$ without spelling it out. The covariance condition is basis-free and determines $\nu$ (see the item `wiener_integral_isometry`).
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 2.3(4), p.3; Theorem 2.9, p.5

import Mathlib
import Definitions.Def_BrownianEnergyRep_WienerPath

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- `ν` is the Wiener measure on `W(𝔤)`, the standard `𝔤`-valued Brownian motion with
covariance given by `⟨·,·⟩` (arXiv:1511.07378v1, Notation 2.3(4), p.3, and Theorem 2.9, p.5).

**Formalization Note** The paper does not spell `ν` out. It is the centred Gaussian measure with
`Cov(⟨a, w_s⟩, ⟨b, w_t⟩) = ⟨a, b⟩ min(s, t)`, a basis-free condition that determines `ν`. -/
structure IsGaussianWienerMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : ℝ) [Fact (0 < T)] (ν : Measure ↥(WienerPath E T)) : Prop where
  isGaussian : IsGaussian ν
  centered : ∀ (a : E), ∀ s ∈ Icc 0 T, ∫ w, ⟪a, wAt w s⟫ ∂ν = 0
  covariance : ∀ (a b : E), ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
    cov[fun w => ⟪a, wAt w s⟫, fun w => ⟪b, wAt w t⟫; ν] = ⟪a, b⟫ * min s t

end BrownianEnergyRep


