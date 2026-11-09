-- Prove2me | Definitions.Def_DerandSq_IsVertexTransitive
-- name    : DerandSq_IsVertexTransitive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:59.174838+00:00
-- url     : https://prove2.me/theorems/8ffd7f64-abb5-4afd-b26f-edbcdad10a8e
-- title:
--   Vertex-transitive graph
-- statement:
--   A simple graph $H$ is **vertex-transitive** if for any two vertices $u, v$ there is a graph automorphism $\varphi$ of $H$ (a bijection of the vertex set preserving adjacency in both directions) with $\varphi(u) = v$.
--
--   Examples are the complete graph $K_d$, cycles, and perfect matchings on an even number of vertices. Vertex-transitivity is the hypothesis on the auxiliary graph $H$ under which the Cohen–Cohen–Maor–Peled bound $\Lambda_H$ applies.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), hypothesis of Theorem 4.1, p.19

import Mathlib

namespace DerandSq

/-- A simple graph `H` is vertex-transitive if its automorphism group acts transitively on its
vertices: for all vertices `u, v` there is a graph automorphism `φ : H ≃g H` with `φ u = v`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), hypothesis of Theorem 4.1, p.19). -/
def IsVertexTransitive {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : H ≃g H, φ u = v

end DerandSq


