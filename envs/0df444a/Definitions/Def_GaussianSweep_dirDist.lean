-- Prove2me | Definitions.Def_GaussianSweep_dirDist
-- name    : GaussianSweep_dirDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:09.391254+00:00
-- url     : https://prove2.me/theorems/dc8c848f-be15-430b-87e5-f5a8fb17e0d2
-- title:
--   Directed distance $D(v,w)$ of Gaussian labels
-- statement:
--   Let every arc $x \to y$ (an ordered pair with $xy \in E(G)$) of a graph $G$ carry a length $\ell(x \to y)$. The **directed distance** $D(v, w)$ is the minimum of
--   $$
--   \sum_{i < k} \ell(x_i \to x_{i+1})
--   $$
--   over all walks $v = x_0, x_1, \dots, x_k = w$, with $D(v,v) = 0$ and $D(v,w) = \infty$ if there is no such walk. In the paper all lengths are positive; then the minimum is attained by a path, and $D$ need not be symmetric.
--
--   **Formalization Note** The value lies in $[0, \infty]$ (`ℝ≥0∞`), as the infimum over all walks of the (nonnegative part of the) summed arc lengths; the lengths are a function on ordered pairs read only along the walk's arcs.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)

import Mathlib
open scoped ENNReal

namespace GaussianSweep

/-- The directed distance `D(v, w)` of Definition 5.2 (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 5.2, p.28 (PDF p.30)):
the minimum of `∑_{i<k} ℓ(xᵢ → xᵢ₊₁)` over all walks `v = x₀, x₁, …, x_k = w`, with `D(v, v) = 0`
and `D(v, w) = ∞` if there is no such walk.

**Formalization Note** The arc lengths are a function `len : V → V → ℝ`, read only on arcs
`x → y` with `xy ∈ E(G)` (the darts of the walk). The value is in `ℝ≥0∞`: the infimum over the
empty set of walks is `⊤ = ∞`, and the trivial walk gives `D(v, v) = 0` for nonnegative lengths.
The paper's lengths are positive, so `ENNReal.ofReal` loses nothing. -/
noncomputable def dirDist {V : Type*} (G : SimpleGraph V) (len : V → V → ℝ) (v w : V) : ℝ≥0∞ :=
  ⨅ p : G.Walk v w, ENNReal.ofReal (p.darts.map fun d => len d.toProd.1 d.toProd.2).sum

end GaussianSweep


