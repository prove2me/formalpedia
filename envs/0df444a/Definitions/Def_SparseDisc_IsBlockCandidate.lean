-- Prove2me | Definitions.Def_SparseDisc_IsBlockCandidate
-- name    : SparseDisc_IsBlockCandidate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:58.942586+00:00
-- url     : https://prove2.me/theorems/36d0b26d-e5ba-4719-8415-86826af88ff2
-- title:
--   Vertex set inducing an edge or a 2-connected graph
-- statement:
--   A vertex set $W$ of a graph $H$ is a **block candidate** if the induced subgraph $H[W]$ is a single edge or 2-connected: $|W| \ge 2$, $H[W]$ is connected, and if $|W| \ge 3$ then $H[W \setminus \{x\}]$ is connected for every $x \in W$.
--
--   This auxiliary notion is used to define the blocks of a graph (maximal 2-connected subgraphs and bridges) as its maximal block candidates.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 1.1, p.4 (blocks)

import Mathlib

namespace SparseDisc

/-- `IsBlockCandidate H W`: the induced subgraph `H[W]` is a single edge or 2-connected — `W` has at
least two vertices, `H[W]` is connected, and if `|W| ≥ 3` then `H[W − x]` is connected for every
`x ∈ W` (auxiliary to the blocks of Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive
Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), p.4: "the blocks are the
maximal 2-connected subgraphs and the bridges"). -/
def IsBlockCandidate {V : Type} [DecidableEq V] (H : SimpleGraph V) (W : Finset V) : Prop :=
  2 ≤ W.card ∧ (H.induce (W : Set V)).Connected ∧
    (3 ≤ W.card → ∀ x ∈ W, (H.induce ((W.erase x : Finset V) : Set V)).Connected)

end SparseDisc


