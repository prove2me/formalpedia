-- Prove2me | Definitions.Def_ShirokovPM_measuresWithBarycenterIn
-- name    : ShirokovPM_measuresWithBarycenterIn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:57.490793+00:00
-- url     : https://prove2.me/theorems/ccfe0d28-1a8e-4951-bf14-1d17994817a9
-- title:
--   Measures with barycenter in a set, $\mathcal P_{\mathcal B}(\mathfrak S(\mathcal H))$
-- statement:
--   Let $\mathcal H$ be a separable complex Hilbert space and $\mathfrak S(\mathcal H)$ the set of density operators (positive trace-class operators of unit trace) with the trace-norm topology. Let $\mathcal P(\mathfrak S(\mathcal H))$ be the set of Borel probability measures on $\mathfrak S(\mathcal H)$ with the topology of weak convergence. The **barycenter** of $\mu\in\mathcal P(\mathfrak S(\mathcal H))$ is the state given by the Bochner integral
--
--   $$
--   \mathbf b(\mu)=\int_{\mathfrak S(\mathcal H)}\sigma\,\mu(d\sigma).
--   $$
--
--   For a set $\mathcal B\subseteq\mathfrak S(\mathcal H)$, the set of **measures with barycenter in $\mathcal B$** is
--
--   $$
--   \mathcal P_{\mathcal B}(\mathfrak S(\mathcal H))=\{\mu\in\mathcal P(\mathfrak S(\mathcal H)) : \mathbf b(\mu)\in\mathcal B\}.
--   $$
--
--   This is the set whose compactness Theorem 1 characterizes.
--
--   **Formalization Note** $\mathcal H$ carries a Hilbert basis $b$, and $\mathfrak S(\mathcal H)$ is the published `QuantumState b` (trace-norm topology, Borel $\sigma$-algebra). $\mathcal P(\mathfrak S(\mathcal H))$ is Mathlib's `ProbabilityMeasure`. "The barycenter of $\mu$ is $\rho$" is the published relation `StateBarycenter b id μ ρ`: every matrix element $\langle x,\sigma y\rangle$ is $\mu$-integrable and $\langle x,\rho y\rangle=\int\langle x,\sigma y\rangle\,\mu(d\sigma)$. This determines the Bochner integral uniquely. No barycenter function is chosen; existence and uniqueness of the barycenter are the milestone `barycenter_existsUnique_mem_closedHull`.
-- source:
--   Shirokov, Properties of probability measures on the set of quantum states and their applications, arXiv:math-ph/0607019v4, §2, p.3 ("For an arbitrary subset ℬ of co̅(𝒜) we denote by 𝒫_ℬ(𝒜) the subset of 𝒫(𝒜) consisting of measures with the barycenter in ℬ", with 𝒜 = 𝔖(ℋ))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

open MeasureTheory
open QAlgorithms.Papers.Independent.Support50.P34

namespace ShirokovPM

/-- **The measures with barycenter in a set**, `𝒫_ℬ(𝔖(ℋ))`. Shirokov, arXiv:math-ph/0607019v4,
§2, p.3: "For an arbitrary subset ℬ of co̅(𝒜) we denote by 𝒫_ℬ(𝒜) the subset of 𝒫(𝒜)
consisting of measures with the barycenter in ℬ", here with `𝒜 = 𝔖(ℋ)` (so `co̅(𝒜) = 𝔖(ℋ)`).

It is the set of Borel probability measures `μ` on the state space `𝔖(ℋ)` whose barycenter
`b(μ) = ∫ σ μ(dσ)` belongs to `B`.

**Formalization Note** `ℋ` is a complex Hilbert space with a Hilbert basis `b` (the platform's
`QuantumState b` is the set of positive trace-class operators of trace one with the trace-norm
topology and its Borel σ-algebra); `𝒫(𝔖(ℋ))` is Mathlib's `ProbabilityMeasure` with the topology
of weak convergence. "The barycenter of `μ` is `ρ`" is the published relation `StateBarycenter b id μ ρ`
(every matrix element `⟨x, σ y⟩` is `μ`-integrable and `⟨x, ρ y⟩ = ∫ ⟨x, σ y⟩ μ(dσ)`), which
characterizes the trace-norm Bochner integral; no barycenter function is chosen here. -/
def measuresWithBarycenterIn {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {I : Type*} (b : HilbertBasis I ℂ H) (B : Set (QuantumState b)) :
    Set (ProbabilityMeasure (QuantumState b)) :=
  {μ | ∃ ρ ∈ B, StateBarycenter b id (μ : Measure (QuantumState b)) ρ}

end ShirokovPM


