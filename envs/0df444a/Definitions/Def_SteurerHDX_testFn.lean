-- Prove2me | Definitions.Def_SteurerHDX_testFn
-- name    : SteurerHDX_testFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:10.559272+00:00
-- url     : https://prove2.me/theorems/cf29bbf7-c520-447e-a3f8-2dda9dff5f93
-- title:
--   The test function $f(\sigma)=\max\{1+\delta-\mathrm{dist}(\sigma,A)/(\varepsilon d),0\}$
-- statement:
--   For a set $A\subseteq\mathcal X(d)$ of facets and parameters $\varepsilon,\delta$, define $f:\mathcal X(d)\to\mathbb R_{\ge0}$ by
--   $$f(\sigma)=\max\Bigl\{1+\delta-\frac{\mathrm{dist}(\sigma,A)}{\varepsilon\cdot d},\,0\Bigr\},$$
--   where $\mathrm{dist}(\sigma,A)$ is the shortest-path distance in $G$ from $\sigma$ to the nearest facet of $A$.
--
--   **Formalization Note** The distance is taken in $\mathbb N\cup\{\infty\}$; when no facet of $A$ is reachable from $\sigma$ it is $\infty$ and $f(\sigma)=0$.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, proof of Theorem 3.1, p.5

import Mathlib
import Definitions.Def_SteurerHDX_facetGraph

namespace SteurerHDX

/-- **The test function f of (3.1).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, proof of Theorem 3.1, p.5: "Define
f : X(d) → ℝ≥0 as follows: f(σ) = max{1 + δ − dist(σ, A)/(ε·d), 0}, ∀σ ∈ X(d), where dist(σ, A)
is the shortest path distance from σ to any facet in A".

**Formalization Note.** dist(σ, A) = min_{a ∈ A} dist_G(σ, a) is computed in `ℕ∞` with
`SimpleGraph.edist` of `facetGraph`; it is `⊤` when no facet of A is reachable from σ (or A is
empty), and then f(σ) = max{1 + δ − ∞, 0} = 0. -/
noncomputable def testFn {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (A : Finset (faces X d)) (ε δ : ℝ) (σ : faces X d) : ℝ :=
  let D : ℕ∞ := ⨅ a ∈ A, (facetGraph X d).edist σ a
  if D = ⊤ then 0 else max (1 + δ - (D.toNat : ℝ) / (ε * d)) 0

end SteurerHDX


