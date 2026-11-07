-- Prove2me | Definitions.Def_SparseDisc_instGraph
-- name    : SparseDisc_instGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:42.795571+00:00
-- url     : https://prove2.me/theorems/c808bfb6-11c9-48a7-b536-f4f6b5ccf562
-- title:
--   Graph $H(G)$ of an instance or constraint system
-- statement:
--   For supports $(U_v)_{v \in V}$, the graph $H$ has vertex set $V$, and distinct $u, v$ are adjacent iff $U_u \cap U_v \ne \emptyset$. For 2-sparse supports this is the simple graph underlying the item multigraph, $H(G)$.
--
--   **Formalization Note** The paper's edges are the pairs $S = \{u, v\}$ with nonempty bundle $B_S$ (items whose set of supports is exactly $S$); for 2-sparse supports an item shared by $u \ne v$ lies in no third support, so the graphs coincide where they are used.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.3 and 'The case t = 2', p.12

import Mathlib

namespace SparseDisc

/-- The graph `H` of an instance or constraint system with supports `(U_v)_{v ∈ V}`: distinct
`u, v` are adjacent iff their supports share an item (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy
Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81),
Definition 2.3 and "The case t = 2", p.12).

**Formalization Note** The paper's edges are the `S = {u, v}` with nonempty bundle
`B_S = {j : {w : j ∈ U_w} = S}`; for 2-sparse supports an item shared by `u ≠ v` lies in no third
support, so the two graphs coincide on 2-sparse supports, the only ones on which it is used. -/
def instGraph {V ι : Type} (U : V → Finset ι) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => ∃ j, j ∈ U u ∧ j ∈ U v)

end SparseDisc


