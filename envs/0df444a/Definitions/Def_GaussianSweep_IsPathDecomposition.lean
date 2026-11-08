-- Prove2me | Definitions.Def_GaussianSweep_IsPathDecomposition
-- name    : GaussianSweep_IsPathDecomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:03.992204+00:00
-- url     : https://prove2.me/theorems/4cf76157-8d5b-44bc-b8ca-f3c911357510
-- title:
--   Path decomposition $W_1,\dots,W_s$ of a graph
-- statement:
--   Let $G$ be a graph. A **path decomposition** of $G$ is a sequence of sets (bags) $W_1, \dots, W_s \subseteq V(G)$, $s \ge 1$, such that
--
--   1. every edge $uv \in E(G)$ has both ends in some bag $W_i$;
--   2. every vertex lies in a nonempty set of consecutive bags: it lies in at least one bag, and if $v \in W_i$ and $v \in W_k$ with $i \le j \le k$, then $v \in W_j$.
--
--   Its **width** is $\max_i |W_i| - 1$. Path decompositions are the objects whose minimum width is the pathwidth.
--
--   **Formalization Note** The sequence is a map $W : \{0, \dots, s-1\} \to \mathrm{Finset}\,V$ with $0 < s$ (0-based indices).
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3, p.12 (PDF p.14); Section 4.1, p.22 (PDF p.24)

import Mathlib

namespace GaussianSweep

/-- A path decomposition of `G` with `s` bags `W 0, …, W (s-1)` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 3,
p.12 (PDF p.14); recalled in Section 4.1, p.22 (PDF p.24)): a nonempty sequence of bags such that
every edge has both ends in some bag, every vertex lies in some bag, and the bags containing a
vertex are consecutive.

**Formalization Note** The sequence `W₁, …, W_s` is `W : Fin s → Finset V` (0-based) with
`0 < s`; "every vertex lies in a nonempty set of consecutive bags" is the conjunction of the third
clause (nonempty) and the fourth (an interval of indices). -/
def IsPathDecomposition {V : Type*} (G : SimpleGraph V) (s : ℕ) (W : Fin s → Finset V) : Prop :=
  0 < s ∧
  (∀ u v, G.Adj u v → ∃ i, u ∈ W i ∧ v ∈ W i) ∧
  (∀ v, ∃ i, v ∈ W i) ∧
  (∀ v (i j k : Fin s), i ≤ j → j ≤ k → v ∈ W i → v ∈ W k → v ∈ W j)

end GaussianSweep


