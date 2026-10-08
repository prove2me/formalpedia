-- Prove2me | Definitions.Def_KernelDRO_Duality_IPM
-- name    : KernelDRO_Duality_IPM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:38.722731+00:00
-- url     : https://prove2.me/theorems/46f4971d-86ee-40fc-a1c7-75cbbfce1c83
-- title:
--   Example 3.5, p. 5 — the integral probability metric $d_{\mathcal F}(P,\hat P)$
-- statement:
--   Let $\mathcal F$ be a class of real functions on $\mathcal X$, $P$ a probability measure on $\mathcal X$, and $\hat P=\frac1N\sum_{i=1}^N\delta_{\xi_i}$ the empirical distribution of samples $\xi_1,\dots,\xi_N\in\mathcal X$. The **integral probability metric** is
--   $$d_{\mathcal F}(P,\hat P)=\sup_{f\in\mathcal F}\int f\,d(P-\hat P)=\sup_{f\in\mathcal F}\Big(\int f\,dP-\frac1N\sum_{i=1}^N f(\xi_i)\Big).$$
--   Choosing $\mathcal F$ as the unit ball of an RKHS gives the MMD, and the 1-Lipschitz functions give the type-1 Wasserstein distance. It defines the IPM-DRO problem (3) and its dual (5).
--
--   **Formalization Note** The supremum is taken in the extended reals ($+\infty$ if unbounded, $-\infty$ for $\mathcal F=\emptyset$). Theorems using it assume $N\ge1$ and that every $f\in\mathcal F$ is continuous on a compact space, so the integral is a genuine one.
-- source:
--   Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally Robust Optimization, arXiv:2006.06981v3, Example 3.5, (3), p. 5; Corollary 3.1.1, p. 5; §2 Notation (empirical distribution), p. 2

import Mathlib

open MeasureTheory

namespace KernelDRO.Duality

/-- The integral probability metric between a probability measure `P` and the empirical
distribution `P̂ = (1/N) Σ_{i=1}^N δ_{ξ_i}` of the samples `ξ_1, …, ξ_N`,
`d_𝓕(P, P̂) := sup_{f∈𝓕} ∫ f d(P − P̂)` (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally
Robust Optimization, arXiv:2006.06981v3, Example 3.5, p. 5, and Corollary 3.1.1, p. 5; `P̂` is defined
in §2 Notation, p. 2).

**Formalization Note.** `∫ f d(P − P̂)` is written `∫ f dP − (1/N) Σ_i f(ξ_i)`. The supremum is
taken in `EReal`, so it is `+∞` when unbounded and `−∞` for the empty class `𝓕 = ∅`. The theorems
using it take `𝓕` to consist of continuous functions on a compact space, so that `∫ f dP` is a
genuine Bochner integral; the number of samples `N` is assumed positive there. -/
noncomputable def ipmDist {X : Type*} [MeasurableSpace X] (F : Set (X → ℝ))
    (P : ProbabilityMeasure X) {N : ℕ} (ξs : Fin N → X) : EReal :=
  ⨆ f ∈ F, (((∫ x, f x ∂(P : Measure X)) - (1 / (N : ℝ)) * (∑ i, f (ξs i)) : ℝ) : EReal)

end KernelDRO.Duality


