-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_IsLegalOrdering
-- name    : CombOpt_MinCut_CapGraph_IsLegalOrdering
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:44.931985+00:00
-- url     : https://prove2.me/theorems/8f4e5e54-7bc7-457b-8835-2a6d70a3d007
-- title:
--   Legal ordering $v_1,\dots,v_n$ of the nodes
-- statement:
--   Let $G=(V,E)$ be a finite capacitated graph. A **legal ordering** of $G$ is an ordering $v_1,v_2,\dots,v_n$ of the nodes of $G$ such that, writing $V_i=\{v_1,\dots,v_i\}$,
--
--   $$u\bigl(\delta(V_{i-1})\cap\delta(v_i)\bigr)\ \ge\ u\bigl(\delta(V_{i-1})\cap\delta(v_j)\bigr)\qquad\text{for } 2\le i<j\le n.$$
--
--   In words: each node $v_i$, $i\ge2$, has at least as much capacity joining it to the earlier nodes $v_1,\dots,v_{i-1}$ as any later node has. Choosing $v_1$ arbitrarily and then repeatedly the node with the largest total capacity of edges to the chosen ones produces a legal ordering. Connectivity of $G$ is not required.
--
--   Legal orderings are the hypothesis of Theorem 3.36 (Nagamochi–Ibaraki, Stoer–Wagner).
--
--   **Formalization Note** An ordering is a bijection `σ : Fin n ≃ V`, 0-based: `σ k` is $v_{k+1}$. The Lean condition for `1 ≤ i < j` in `Fin n` with $P=\{\sigma k : k<i\}$ is the book's condition for the pair $(i+1,j+1)$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.5.1, p. 74 (PDF p. 83)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta

namespace CombOpt.MinCut

open Classical in
/-- **Legal ordering.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.5.1,
p. 74 (PDF p. 83): "A legal ordering of G is an ordering v₁, v₂, …, vₙ of the nodes of G such
that, where Vᵢ denotes {v₁, …, vᵢ},
u(δ(V_{i−1}) ∩ δ(vᵢ)) ≥ u(δ(V_{i−1}) ∩ δ(vⱼ)) for 2 ≤ i < j ≤ n."

An ordering of the nodes is a bijection `σ : Fin n ≃ V`, with `σ k` the book's `v_{k+1}`.
`G.IsLegalOrdering σ` says: for all `i < j` in `Fin n` with `1 ≤ i`, writing
`P = {σ k : k < i} = {v₁, …, v_i}` (the book's `V_{(i+1)−1}`),
`u(δ(P) ∩ δ(σ j)) ≤ u(δ(P) ∩ δ(σ i))`; this is the book's inequality for the pair
`(i + 1, j + 1)`, and `1 ≤ i < j ≤ n − 1` is `2 ≤ i + 1 < j + 1 ≤ n`.

**Formalization Note.** Indices are 0-based: the book's condition for `(i, j)` with
`2 ≤ i < j ≤ n` is the Lean condition for `(i − 1, j − 1)`. Connectivity of `G` is not required,
as in the book (p. 75: "the definition of 'legal ordering' does not require the connectivity of
G"). Since `σ` is a bijection, `n` is the number of nodes. -/
def CapGraph.IsLegalOrdering {V E : Type*} [Fintype E] (G : CapGraph V E) {n : ℕ}
    (σ : Fin n ≃ V) : Prop :=
  ∀ i j : Fin n, 1 ≤ i.val → i < j →
    G.uSum (G.delta ((Finset.univ.filter (fun k : Fin n => k < i)).map σ.toEmbedding) ∩
        G.delta {σ j}) ≤
      G.uSum (G.delta ((Finset.univ.filter (fun k : Fin n => k < i)).map σ.toEmbedding) ∩
        G.delta {σ i})

end CombOpt.MinCut


