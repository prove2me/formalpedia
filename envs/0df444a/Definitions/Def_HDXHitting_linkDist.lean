-- Prove2me | Definitions.Def_HDXHitting_linkDist
-- name    : HDXHitting_linkDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:48.965937+00:00
-- url     : https://prove2.me/theorems/a1a204db-2bbf-4716-a4f0-a114abe2bba7
-- title:
--   Top distribution $\pi_{\tau,k}$ of the link $X_\tau$
-- statement:
--   Let $p$ be a top distribution and $\tau$ a face, i.e. $\Pr_{\sigma\sim p}[\tau\subseteq\sigma]>0$. The **link** $X_\tau$ is the complex whose maximal faces are the sets $\sigma$ disjoint from $\tau$ with $\sigma\cup\tau\in X(d)$, with top distribution
--   $$
--   \pi_{\tau}(\sigma) = \frac{p(\tau\cup\sigma)}{\Pr_{\sigma'\sim p}[\tau\subseteq\sigma']}\quad\text{for }\sigma\cap\tau=\emptyset,\qquad \pi_\tau(\sigma) = 0\ \text{otherwise}.
--   $$
--   If $\tau$ has codimension $k$, the link is a $k$-dimensional complex. The vertex link $X_v$ used in the induction of Lemma 3.2 is the case $\tau=\{v\}$.
--
--   **Formalization Note** For a non-face $\tau$ the denominator is $0$ and Lean returns the zero function; the results use the link only at faces.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, p.12 (π_{τ,k}(σ) ∝ π_d(τ ∪ σ)1(τ ∪ σ ∈ X(d)))

import Mathlib

namespace HDXHitting

/-- The top distribution `π_{τ,k}` of the link `X_τ` of a face `τ` (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), §2.2.1, p.12:
the link of `τ` has maximal faces `{σ ∈ X : σ ∩ τ = ∅ and σ ∪ τ ∈ X(d)}` and distribution
`π_{τ,k}(σ) ∝ π_d(τ ∪ σ) 1(τ ∪ σ ∈ X(d))`): for `σ` disjoint from `τ`,
`π_{τ,k}(σ) = p(τ ∪ σ) / Pr_{σ'∼p}[τ ⊆ σ']`, and `0` otherwise. The vertex link `X_v` is the
case `τ = {v}`.

**Formalization Note** Used for faces, i.e. `Pr[τ ⊆ σ'] > 0`; for a non-face the division is by
`0` and the function is `0`. -/
noncomputable def linkDist {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (τ : Finset V) (σ : Finset V) : ℝ :=
  if Disjoint τ σ then
    p (τ ∪ σ) / ∑ σ' ∈ Finset.univ.filter (fun σ' : Finset V => τ ⊆ σ'), p σ'
  else 0

end HDXHitting


