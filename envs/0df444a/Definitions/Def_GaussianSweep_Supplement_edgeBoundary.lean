-- Prove2me | Definitions.Def_GaussianSweep_Supplement_edgeBoundary
-- name    : GaussianSweep_Supplement_edgeBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:33:00.551704+00:00
-- url     : https://prove2.me/theorems/e6b171f3-bdf3-491d-b150-63bf576c9949
-- title:
--   Edge boundary count $e(X)$
-- statement:
--   For a graph $G$ and a set $X \subseteq V(G)$, $e(X)$ is the number of edges of $G$ with exactly one end in $X$:
--   $$
--   e(X) = \big|\{uv \in E(G) : u \in X,\ v \notin X\}\big| .
--   $$
--   It is the quantity whose maximum over the prefixes of an ordering defines the cutwidth, and whose minimum over balanced sets defines the bisection width.
--
--   **Formalization Note** Each such edge is counted once, as the ordered pair $(u,v)$ with $u \in X$, $v \notin X$, $u \sim v$. The cardinality is `Set.ncard`, exact on the finite vertex types used throughout.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)

import Mathlib

namespace GaussianSweep.Supplement

/-- The edge boundary count `e(X)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14)):
for `X ⊆ V(G)`, the number of edges of `G` with exactly one end in `X`.

**Formalization Note** An edge with exactly one end in `X` is counted once, as the ordered pair
`(u, v)` with `u ∈ X`, `v ∉ X` and `u ~ v` (the orientation from the end in `X` is unique).
`X` is a `Set V`; `Set.ncard` is the cardinality, exact on a finite vertex type, which is the
only case used. -/
noncomputable def edgeBoundary {V : Type*} (G : SimpleGraph V) (X : Set V) : ℕ :=
  {p : V × V | p.1 ∈ X ∧ p.2 ∉ X ∧ G.Adj p.1 p.2}.ncard

end GaussianSweep.Supplement


