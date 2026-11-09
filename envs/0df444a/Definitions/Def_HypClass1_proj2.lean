-- Prove2me | Definitions.Def_HypClass1_proj2
-- name    : HypClass1_proj2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:45.206207+00:00
-- url     : https://prove2.me/theorems/460ca9bf-3dbe-49c3-8b77-af08b1f7e7b2
-- title:
--   Bipartite projection $\Xi^{(2)}(H)$
-- statement:
--   Given a bipartite structure $\Xi = (X, Y, Z, M, E)$ and a 3-graph $H$ on the same vertex set, $\Xi^{(3)}(H) = H \cap E$ is the bipartite projection of $H$. Seen as a bipartite graph $\Xi^{(2)}(H)$, its vertex set is $M \cup Z$ and each edge $\{x, y, z\} \in \Xi^{(3)}(H)$ with $\{x,y\} \in M$, $z \in Z$ becomes the edge $(\{x,y\}, z)$.
--
--   Lemma 5.2 shows that the projection of a pseudorandom 3-graph by a random bipartite structure is a pseudorandom bipartite graph.
--
--   **Formalization Note** Edges are pairs $(m, z) \in M \times Z$ with $m \cup \{z\} \in H \cap E$; the parts are $M$ and $Z$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §5 p.11

import Mathlib

namespace HypClass1

/-- **Bipartite projection** `Ξ^{(2)}(H)`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §5 p.11: "Given a bipartite structure Ξ = (X, Y, Z, M, E)
and a 3-graph H on the same set of vertices, let Ξ^{(3)}(H) := H ∩ E be the bipartite projection of H
with respect to Ξ. … one can see it as a bipartite graph Ξ^{(2)}(H) by considering the set of vertices
to be M ∪ Z and the projection map π : Ξ^{(3)}(H) → Ξ^{(2)}(H) given by π(x, y, z) = ({x, y}, z)."

`proj2 H M Z E` is the bipartite graph with parts `M` and `Z` whose edges are the pairs `(m, z)` with
`m ∪ {z} ∈ H ∩ E`.

**Formalization Note.** Edges are pairs in `M × Z`, so the vertex set `V(Ξ^{(2)}(H))` is `M ∪ Z` with
parts `M` and `Z` (both of size `n/3` for a bipartite structure). -/
def proj2 {V : Type*} [DecidableEq V] (H M : Finset (Finset V)) (Z : Finset V)
    (E : Finset (Finset V)) : Finset (Finset V × V) :=
  (M ×ˢ Z).filter (fun mz => insert mz.2 mz.1 ∈ H ∩ E)

end HypClass1


