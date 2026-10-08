-- Prove2me | Definitions.Def_SnarkGen_EdgeInsertion_insertEdge
-- name    : SnarkGen_EdgeInsertion_insertEdge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:05:25.081981+00:00
-- url     : https://prove2.me/theorems/6cc1bb4d-a257-4f80-8d59-e18538c5ac0f
-- title:
--   The edge insertion operation, Figure 1(d) (p. 5)
-- statement:
--   Let $G = (V,E)$ be a simple graph and let $e = ab$ and $e' = cd$ be two distinct edges of $G$; the two edges may share an end-vertex (Figure 1(d): "can be the same vertex"). The **edge insertion operation** applied to $e$ and $e'$ produces the graph $G'$ obtained by
--
--   1. subdividing $e$ with a new vertex $x$ (replacing $ab$ by the path $a\,x\,b$),
--   2. subdividing $e'$ with a new vertex $y$ (replacing $cd$ by the path $c\,y\,d$), and
--   3. joining the two new vertices by a new edge $xy$.
--
--   Thus $V(G') = V \cup \{x, y\}$ and
--   $$E(G') = \bigl(E \setminus \{e, e'\}\bigr) \cup \{ax, xb, cy, yd, xy\}.$$
--   If $G$ is cubic, so is $G'$: the end-vertices of $e$ and $e'$ keep degree $3$ (a shared end-vertex loses its two old edges and gains $x$ and $y$), and $x$, $y$ have degree $3$. This is the last operation in the generation of cubic graphs of girth at least 4 used in §3.1, and it is the operation whose colourability the look-ahead criteria of Lemma 3.2, Theorem 3.3 and Theorem 3.4 decide.
--
--   **Formalization Note** The new graph has vertex type `V ⊕ Fin 2`: `Sum.inl v` is the old vertex $v$, `Sum.inr 0` is $x$ and `Sum.inr 1` is $y$. Edges are given as unordered pairs `e e' : Sym2 V`. Adjacency: `inl u ~ inl v` iff $uv \in E$ and $uv \notin \{e, e'\}$; `inl u ~ inr 0` iff $u \in e$; `inl u ~ inr 1` iff $u \in e'$; `inr 0 ~ inr 1`. The definition accepts any `e, e'`; the theorems that use it assume that $e$ and $e'$ are distinct edges of $G$. A decidability instance is provided for computation on concrete graphs.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 5, Figure 1(d) and §3.1 (proof note of Lemma 3.2)

import Mathlib

namespace SnarkGen.EdgeInsertion

variable {V : Type*}

/-- Adjacency of the **edge insertion operation** (operation (d) of Figure 1,
arXiv:1206.6690v3, p. 5). The new graph has vertex type `V ⊕ Fin 2`: `inl v` is the old vertex
`v`, `inr 0` is the new vertex subdividing `e`, and `inr 1` the new vertex subdividing `e'`.
* `inl u ~ inl v` iff `u ~ v` in `G` and the edge `uv` is neither `e` nor `e'`;
* `inl u ~ inr 0` iff `u` is an end-vertex of `e`, and `inl u ~ inr 1` iff `u` is an end-vertex
  of `e'` (and symmetrically);
* `inr 0 ~ inr 1` (the inserted edge). -/
def insertEdgeAdj (G : SimpleGraph V) (e e' : Sym2 V) : V ⊕ Fin 2 → V ⊕ Fin 2 → Prop
  | .inl u, .inl v => G.Adj u v ∧ s(u, v) ≠ e ∧ s(u, v) ≠ e'
  | .inl u, .inr k => u ∈ ![e, e'] k
  | .inr k, .inl u => u ∈ ![e, e'] k
  | .inr k, .inr l => k ≠ l

/-- The graph `G'` obtained from `G` by the **edge insertion operation** applied to two edges
`e`, `e'` of `G` (arXiv:1206.6690v3, p. 5, Figure 1(d), Lemma 3.2, Theorem 3.3): both edges are
subdivided by a new vertex (`inr 0` on `e`, `inr 1` on `e'`) and the two new vertices are joined
by a new edge. The two edges may share an end-vertex ("can be the same vertex", Figure 1(d)).
The operation is meant for two distinct edges `e ≠ e'` of `G`; the statements that use it carry
these hypotheses. -/
def insertEdge (G : SimpleGraph V) (e e' : Sym2 V) : SimpleGraph (V ⊕ Fin 2) where
  Adj := insertEdgeAdj G e e'
  symm := by
    constructor
    rintro (u | k) (v | l) h
    · refine ⟨h.1.symm, ?_, ?_⟩
      · rw [Sym2.eq_swap]; exact h.2.1
      · rw [Sym2.eq_swap]; exact h.2.2
    · exact h
    · exact h
    · exact Ne.symm h
  loopless := by
    constructor
    rintro (u | k) h
    · exact h.1.ne rfl
    · exact h rfl

instance [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (e e' : Sym2 V) :
    DecidableRel (insertEdge G e e').Adj := fun x y =>
  match x, y with
  | .inl u, .inl v => inferInstanceAs (Decidable (G.Adj u v ∧ s(u, v) ≠ e ∧ s(u, v) ≠ e'))
  | .inl u, .inr k => inferInstanceAs (Decidable (u ∈ ![e, e'] k))
  | .inr k, .inl u => inferInstanceAs (Decidable (u ∈ ![e, e'] k))
  | .inr k, .inr l => inferInstanceAs (Decidable (k ≠ l))

end SnarkGen.EdgeInsertion


