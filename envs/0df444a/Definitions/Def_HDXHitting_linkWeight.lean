-- Prove2me | Definitions.Def_HDXHitting_linkWeight
-- name    : HDXHitting_linkWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:30.812372+00:00
-- url     : https://prove2.me/theorems/765dceb9-3fb0-4f2f-a27d-7bb166305642
-- title:
--   Edge weights of the induced graph of the link $X_\tau$
-- statement:
--   Let $p$ be a top distribution and $\tau$ a set of vertices. For vertices $u\ne w$ outside $\tau$, the **link edge weight** is
--   $$
--   W_\tau(u,w) = \Pr_{\sigma\sim p}\big[\tau\cup\{u,w\}\subseteq\sigma\big],
--   $$
--   and $W_\tau(u,w) = 0$ otherwise. Up to a positive factor depending only on $\tau$, $W_\tau$ is the edge distribution $\pi_{\tau,2}$ of the induced graph $(X_\tau(1),X_\tau(2))$ of the link of $\tau$, since $\pi_{\tau,2}(\{u,w\})\propto \pi_{|\tau|+2}(\tau\cup\{u,w\})$.
--
--   These weights carry the spectral conditions of Definition 2.2.
--
--   **Formalization Note** The weights are not normalized: the random walk $D^{-1}W_\tau$, and hence every eigenvalue or singular value of the link graph, is unchanged by a positive factor. Each unordered edge is counted in both orientations. For a non-face $\tau$ all weights are $0$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, p.12 (links and the induced graph)

import Mathlib

namespace HDXHitting

/-- The edge weights of the induced graph `(X_τ(1), X_τ(2))` of the link of `τ` (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3),
§2.2.1, p.12: `π_{τ,i}(σ) ∝ π_{d−k+i}(τ ∪ σ) 1(τ ∪ σ ∈ X(d − k + i))`, and the induced graph
of a complex, p.12): for distinct `u, w ∉ τ` the weight is `Pr_{σ∼p}[τ ∪ {u, w} ⊆ σ]`, and `0`
otherwise.

**Formalization Note** The weights are unnormalized: they equal the link's edge distribution
`π_{τ,2}` (counted once per orientation) times a factor depending only on `τ`. The random walk
`D⁻¹A` of the link graph, and hence its spectrum, does not see this factor. For `τ` not a face
all weights vanish. -/
noncomputable def linkWeight {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (τ : Finset V) (u w : V) : ℝ :=
  if u ≠ w ∧ u ∉ τ ∧ w ∉ τ then
    ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => insert u (insert w τ) ⊆ σ), p σ
  else 0

end HDXHitting


