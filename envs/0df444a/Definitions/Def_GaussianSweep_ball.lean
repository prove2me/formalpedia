-- Prove2me | Definitions.Def_GaussianSweep_ball
-- name    : GaussianSweep_ball
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:05.821205+00:00
-- url     : https://prove2.me/theorems/e1deb717-95a4-4d27-80cf-bec8475e014d
-- title:
--   Ball $B_k(v)$ of radius $k$
-- statement:
--   For a vertex $v$ of a graph $G$ and $k \in \mathbb N$, the **ball** of radius $k$ is
--   $$
--   B_k(v) = \{w \in V(G) : \mathrm{dist}(v, w) \le k\},
--   $$
--   where $\mathrm{dist}(v, w) \in \mathbb N \cup \{\infty\}$ is the number of edges of a shortest $v$–$w$ path ($\infty$ if there is none).
--
--   **Formalization Note** The distance is Mathlib's extended distance `SimpleGraph.edist`, which is $\infty$ across components (the integer-valued `SimpleGraph.dist` is $0$ there and is not used).
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.1, p.22 (PDF p.24)

import Mathlib

namespace GaussianSweep

/-- The ball `B_k(v) = {w : dist(v, w) ≤ k}` of radius `k` around `v` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 4.1,
p.22 (PDF p.24)), where `dist(v, w) ∈ ℕ ∪ {∞}` is the number of edges of a shortest `v`–`w` path.

**Formalization Note** The distance is Mathlib's `SimpleGraph.edist` (`⊤` across components),
not `SimpleGraph.dist` (which is `0` across components). -/
noncomputable def ball {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V) (k : ℕ) : Finset V :=
  by classical exact Finset.univ.filter fun w => G.edist v w ≤ (k : ℕ∞)

end GaussianSweep


