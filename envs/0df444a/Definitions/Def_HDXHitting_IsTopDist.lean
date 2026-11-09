-- Prove2me | Definitions.Def_HDXHitting_IsTopDist
-- name    : HDXHitting_IsTopDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:27.183028+00:00
-- url     : https://prove2.me/theorems/8ecbc981-5af1-4d47-8653-c27e4326e4dd
-- title:
--   Top distribution $\pi_d$ of a $d$-dimensional complex
-- statement:
--   Let $V$ be a finite vertex set. A **$d$-dimensional (pure, simplicial) complex** $(X,\pi)$ is determined by its **top distribution** $\pi_d$: a function $p$ on the subsets of $V$ such that
--   $$
--   p(\sigma)\ge 0\ \text{for all }\sigma,\qquad p(\sigma)\ne 0\ \Rightarrow\ |\sigma| = d,\qquad \sum_{\sigma\subseteq V} p(\sigma) = 1 .
--   $$
--   The maximal faces $X(d)$ are the $d$-sets $\sigma$ with $p(\sigma)>0$, the complex $X$ is their downward closure, and the distributions $\pi_k$ on the $k$-faces are induced by $p$ via $\pi_k(\tau)\propto \Pr_{\sigma\sim p}[\tau\subseteq\sigma]$.
--
--   All objects of the mission (vertex measure, links, spectral conditions, colourings) are defined from such a $p$.
--
--   **Formalization Note** The dimension of a face is its number of vertices, as in the paper (footnote 9): top faces have $d$ elements. No regularity, connectivity or uniformity is assumed.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, pp.11–12

import Mathlib

namespace HDXHitting

/-- The top distribution `π_d` of a `d`-dimensional (pure, simplicial) complex (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3),
§2.2.1, pp.11–12): a function `p` on the finite subsets of the vertex type `V` that is
nonnegative, vanishes off the `d`-element sets, and has total mass `1`. The complex `(X, π)` is
encoded by `p` alone: its maximal faces `X(d)` are the sets `σ` with `p σ ≠ 0`, `X` is their
downward closure, and the lower distributions `π_k` are induced by `p`.

**Formalization Note** Dimension = number of vertices (p.11, footnote 9: `X(i)` are the
`i`-element faces). A `d`-set with `p σ = 0` is simply not a face. Positivity of `π_d` on its
support is automatic, and no regularity or connectivity is assumed. -/
def IsTopDist {V : Type*} [Fintype V] (d : ℕ) (p : Finset V → ℝ) : Prop :=
  (∀ σ, 0 ≤ p σ) ∧ (∀ σ, p σ ≠ 0 → σ.card = d) ∧ ∑ σ : Finset V, p σ = 1

end HDXHitting


