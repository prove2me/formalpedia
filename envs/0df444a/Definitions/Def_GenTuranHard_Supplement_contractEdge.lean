-- Prove2me | Definitions.Def_GenTuranHard_Supplement_contractEdge
-- name    : GenTuranHard_Supplement_contractEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:39:35.841209+00:00
-- url     : https://prove2.me/theorems/04695354-fc2b-4348-9bfb-566fe2565161
-- title:
--   Edge contraction $T/e$ of a simple graph
-- statement:
--   Let $T$ be a finite simple graph and $e = uv$ an edge of $T$. The graph $T/e$ obtained from $T$ by **contracting the edge** $e$ deletes the edge $e$ and replaces the two vertices $u$ and $v$ by a single new vertex that is adjacent precisely to the vertices which were adjacent to $u$ or to $v$ in $T$. All other adjacencies of $T$ are kept. The result is again a simple graph: the edge $uv$ disappears (no loop) and a common neighbour of $u$ and $v$ is joined to the new vertex once (no parallel edges). Thus
--
--   $$
--   V(T/e) = \bigl(V(T)\setminus\{u,v\}\bigr)\cup\{w\},\qquad N_{T/e}(w) = \bigl(N_T(u)\cup N_T(v)\bigr)\setminus\{u,v\}.
--   $$
--
--   This is the graph whose chromatic number $\chi(T/e)$ appears in the hypothesis of Theorem 5.1, and the inequality $\chi(T/e) \le \chi(T) + 1$ is what makes Theorem 1.7 a corollary of Theorem 5.1.
--
--   **Formalization Note** The vertex set is encoded as $V(T)\setminus\{v\}$, with the vertex $u$ standing for the merged vertex $w$. Two distinct vertices $a, b$ are adjacent iff $ab \in E(T)$, or one of them is $u$ and the other is a neighbour of $v$ in $T$. This graph is isomorphic to the one described above, and only isomorphism-invariant quantities are used. The definition is total in $u, v$ but is used only for an edge $uv$ of $T$.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §5, p.22 (definition of T/e)

import Mathlib

set_option autoImplicit false

namespace GenTuranHard

namespace Supplement

/-- The **edge contraction** `T/e` of the edge `e = uv` of `T` (Chen, He, Li, Ma, Xie, *NP-hardness of
additive approximation for generalized Turán problems*, arXiv:2610.16358, sha256 dc85633a…, §5, p.22):
"`T/e` [is] the graph obtained from `T` by contracting the edge `e`, that is, deleting the edge `e` and
replacing vertices `u` and `v` by a single vertex adjacent precisely to the vertices which were adjacent
to either `u` or `v` in `T`."

The vertex set is `V(T) \ {v}`, and the vertex `u` plays the role of the merged vertex. Two vertices
`a ≠ b` of `V(T) \ {v}` are adjacent iff they are adjacent in `T`, or one of them is the merged vertex
`u` and the other is a neighbour of `v` in `T`. Hence the merged vertex is adjacent exactly to
`(N_T(u) ∪ N_T(v)) \ {u, v}`, all other adjacencies of `T − {u, v}` are kept, and the result is simple
(no loop, no parallel edge).

**Formalization Note** The source's vertex set `(V(T) \ {u, v}) ∪ {new vertex}` is encoded as
`{w // w ≠ v}`, with `u` standing for the new vertex; the two graphs are isomorphic, and only
isomorphism-invariant quantities (the chromatic number) are used. The definition is meant for an edge
`uv` of `T` (`T.Adj u v`, so `u ≠ v`); it is total in `u, v`. -/
def contractEdge {W : Type} (T : SimpleGraph W) (u v : W) : SimpleGraph {w : W // w ≠ v} where
  Adj a b := a ≠ b ∧
    (T.Adj a.1 b.1 ∨ (a.1 = u ∧ T.Adj v b.1) ∨ (b.1 = u ∧ T.Adj v a.1))
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h2 | h2 | h2
    · exact Or.inl (T.adj_symm h2)
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h2)⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

end Supplement

end GenTuranHard


