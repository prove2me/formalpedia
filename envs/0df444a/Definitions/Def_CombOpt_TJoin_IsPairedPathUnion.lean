-- Prove2me | Definitions.Def_CombOpt_TJoin_IsPairedPathUnion
-- name    : CombOpt_TJoin_IsPairedPathUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:03:45.135981+00:00
-- url     : https://prove2.me/theorems/4324496b-53cb-4291-99f7-a79ae59089a9
-- title:
--   Union of $|T|/2$ edge-disjoint paths joining $T$ in pairs
-- statement:
--   Let $T$ be a set of nodes and $J$ a set of edges, and fix a kind of path (for instance simple paths, or shortest paths). $J$ is the **union of the edge sets of $|T|/2$ edge-disjoint paths joining the nodes of $T$ in pairs** if there are pairs $(a_1,b_1),\dots,(a_{|T|/2},b_{|T|/2})$ of distinct nodes of $T$ such that every node of $T$ occurs in exactly one pair, and edge sets $P_1,\dots,P_{|T|/2}$ where $P_i$ is the edge set of a path of the given kind from $a_i$ to $b_i$, the $P_i$ are pairwise disjoint, and
--
--   $$J=P_1\cup\dots\cup P_{|T|/2}.$$
--
--   **Formalization Note** The kind of path is a parameter `Q u v P`; Proposition 5.25 uses simple paths and Proposition 5.26 shortest paths.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 5.25, p. 169 (PDF p. 177)

import Mathlib

namespace CombOpt.TJoin

/-- **Union of |T|/2 edge-disjoint paths joining the nodes of T in pairs.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.4, p. 169 (PDF p. 177), Proposition 5.25: "the union of the edge-sets of |T|/2
edge-disjoint simple paths, which join the nodes in T in pairs".

`IsPairedPathUnion T J Q` holds when there are `|T|/2` pairs `(aᵢ, bᵢ)` of distinct nodes of
`T`, every node of `T` occurring in exactly one pair, and edge sets `Pᵢ` with `Q aᵢ bᵢ Pᵢ`
(`Pᵢ` is a path of the required kind from `aᵢ` to `bᵢ`), pairwise disjoint, whose union is `J`.

**Formalization Note.** `Q` is the kind of path: `G.IsSimplePath` in Proposition 5.25,
`G.IsShortestPath c` in Proposition 5.26. Pairs are indexed by `Fin (T.card / 2)`. -/
def IsPairedPathUnion {V E : Type*} [DecidableEq E] (T : Finset V) (J : Finset E) (Q : V → V → Finset E → Prop) : Prop :=
  ∃ (a b : Fin (T.card / 2) → V) (P : Fin (T.card / 2) → Finset E),
    (∀ i, a i ∈ T ∧ b i ∈ T ∧ a i ≠ b i) ∧
    (∀ t ∈ T, ∃! i, a i = t ∨ b i = t) ∧
    (∀ i, Q (a i) (b i) (P i)) ∧
    (Pairwise fun i j => Disjoint (P i) (P j)) ∧
    J = Finset.univ.biUnion P

end CombOpt.TJoin


