-- Prove2me | Definitions.Def_StochApproxDyn_WeakAPT_InvariantMeasures
-- name    : StochApproxDyn_WeakAPT_InvariantMeasures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:04:44.938274+00:00
-- url     : https://prove2.me/theorems/fb2b6d1e-a212-4c55-a66e-d185bdbf0e66
-- title:
--   The set $\mathcal M(\Phi)$ of $\Phi$-invariant Borel probability measures of a semiflow (§8.3, §10)
-- statement:
--   Let $(M,d)$ be a metric space with its Borel $\sigma$-algebra and let $\Phi:\mathbb R_+\times M\to M$, $(t,x)\mapsto\Phi_t(x)$, be a **semiflow**: a continuous map with $\Phi_0=\mathrm{Id}$ and $\Phi_{t+s}=\Phi_t\circ\Phi_s$ for all $t,s\ge0$.
--
--   Write $\mathcal P(M)$ for the space of Borel probability measures on $M$ with the topology of weak convergence (the one a functional analyst would call weak$^*$). A measure $\mu\in\mathcal P(M)$ is **$\Phi$-invariant** if
--   $$(\Phi_t)_*\mu=\mu\qquad\text{for every } t\ge 0,$$
--   that is, $\mu(\Phi_t^{-1}(A))=\mu(A)$ for every Borel set $A\subset M$ and every $t\ge0$; equivalently $\int f\circ\Phi_t\,d\mu=\int f\,d\mu$ for every bounded continuous $f$. The set of invariant measures is denoted $\mathcal M(\Phi)\subset\mathcal P(M)$.
--
--   $\mathcal M(\Phi)$ is the target set of Theorem 10.1: weak limit points of the occupation measures of a weak asymptotic pseudotrajectory lie in it.
--
--   **Formalization Note** Section 8.3 of the notes states invariance for flows ($t\in\mathbb R$) as $\mu(A)=\mu(\Phi_t(A))$. For a semiflow the images $\Phi_t(A)$ of Borel sets need not be Borel, and the proof of Theorem 10.1 (p. 63) establishes invariance as $\int f\circ\Phi_T\,d\mu=\int f\,d\mu$, i.e. in the push-forward form used here; for a flow the two definitions coincide. $\mathcal P(M)$ is Mathlib's `ProbabilityMeasure M`, whose topology is that of weak convergence. The semiflow is Mathlib's `Flow ℝ≥0 M`.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 3, p. 9 (PDF p. 10), definition of a semiflow; Section 8.3, p. 43 (PDF p. 44), definition of P(M) and M(Φ); Section 10, p. 61 (PDF p. 62)

import Mathlib

namespace StochApproxDyn.WeakAPT

open MeasureTheory
open scoped NNReal

/-- The set `𝓜(Φ) ⊂ 𝓟(M)` of `Φ`-invariant Borel probability measures of a semiflow
`Φ : ℝ≥0 × M → M` (Benaïm 1999, §8.3, p. 43, and §10, p. 61). For a semiflow, invariance is
taken in the push-forward sense `(Φ_t)_* μ = μ` for every `t ≥ 0`, i.e. `μ(Φ_t⁻¹(A)) = μ(A)` for
every Borel set `A` and every `t ≥ 0`; this is the form used in the proof of Theorem 10.1
(`∫ f ∘ Φ_T dμ = ∫ f dμ`, p. 63). For a flow it coincides with the definition
`μ(A) = μ(Φ_t(A))` for all `t ∈ ℝ` of §8.3. `ProbabilityMeasure M` carries Mathlib's topology of
weak convergence (convergence against bounded continuous functions). -/
def invariantMeasures {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (Φ : Flow ℝ≥0 M) : Set (ProbabilityMeasure M) :=
  {μ | ∀ t : ℝ≥0, (μ : Measure M).map (Φ t) = (μ : Measure M)}

end StochApproxDyn.WeakAPT


