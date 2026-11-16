-- Prove2me | Definitions.Def_ARTreeCover_Supplement_IsVertexSeparable
-- name    : ARTreeCover_Supplement_IsVertexSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:00:26.663017+00:00
-- url     : https://prove2.me/theorems/932a76ab-ec25-4b23-aae9-db42dc89f7bc
-- title:
--   $s$-vertex-separable graphs
-- statement:
--   A weighted graph $G$ is **$s$-vertex-separable** if every sub-graph $(U,G')$ of $G$ has a balanced vertex separator $S\subseteq U$ with $|S|\le s$.
--
--   Bounded treewidth and other hereditary classes are vertex-separable; Theorems 18, 26 and 40 use this hypothesis.
--
--   **Formalization Note** Definition 5 allows the bound to be a function $s(\theta)$ of the sub-graph's size $\theta$. The theorems that use the notion treat $s$ as a single number (the path-clusters graph "contains at most $s$ vertices", p.25, and the bounds involve $s^{1/k}$), so $s\in\mathbb N$ bounds the separator of every sub-graph, i.e. the constant function $s(\theta)=s$.
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 5, p.10 (PDF p.13)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_Supplement_IsBalancedSep

namespace ARTreeCover.Supplement

open ARTreeCover

/-- `IsVertexSeparable G s`: `G` is `s`-vertex-separable, i.e. every sub-graph of `G` has a
balanced vertex separator with at most `s` vertices.

Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…), Definition 5, p.10 (PDF p.13): "we say that G
is s-vertex-separable for some function s = s(θ), if every sub-graph of G with θ vertices has a
separator of size at most s(θ)."

**Formalization Note.** Definition 5 allows a function `s(θ)` of the sub-graph's size; Theorems 18,
26 and 40, the only places the notion is used, treat `s` as one number ("contains at most s
vertices", p.25; the bound `s^{1/k}`), so `s : ℕ` bounds the separator of every sub-graph (the
constant function `s(θ) = s`). Sub-graphs are `IsSubgraph`; separators are `IsBalancedSep` with
respect to the sub-graph's own vertex count. -/
def IsVertexSeparable {V : Type} (G : WGraph V) (s : ℕ) : Prop :=
  ∀ (U : Set V) (G' : WGraph V), IsSubgraph G U G' →
    ∃ S : Set V, IsBalancedSep G'.graph U S ∧ S.ncard ≤ s

end ARTreeCover.Supplement


