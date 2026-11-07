-- Prove2me | Definitions.Def_SparseDisc_IsSubgraphOfKqn
-- name    : SparseDisc_IsSubgraphOfKqn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:32.997623+00:00
-- url     : https://prove2.me/theorems/8772ab17-4dc2-41b1-a3ef-2a5a04d81d3e
-- title:
--   Subgraph of $K_{q,n}$
-- statement:
--   A graph $H$ is a **subgraph of $K_{q,n}$** (for some $n$) if there is an injective map from its vertices into the vertices of the complete bipartite graph $K_{q,n}$ that sends edges to edges.
--
--   **Formalization Note** A subgraph is an injective homomorphism into `completeBipartiteGraph (Fin q) (Fin n)`, not a graph embedding (which would also reflect non-edges and describe induced copies only).
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(b), p.5

import Mathlib

namespace SparseDisc

/-- `IsSubgraphOfKqn H q`: `H` is (isomorphic to) a **subgraph of `K_{q,n}`** for some `n`
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Theorem 1.9(b), p.5: "subgraphs of Kq,n").

**Formalization Note** A subgraph is an injective homomorphism into
`completeBipartiteGraph (Fin q) (Fin n)` (not an embedding `↪g`, which would reflect adjacency and
describe induced copies only). -/
def IsSubgraphOfKqn {V : Type} (H : SimpleGraph V) (q : ℕ) : Prop :=
  ∃ (n : ℕ) (φ : H →g completeBipartiteGraph (Fin q) (Fin n)), Function.Injective φ

end SparseDisc


