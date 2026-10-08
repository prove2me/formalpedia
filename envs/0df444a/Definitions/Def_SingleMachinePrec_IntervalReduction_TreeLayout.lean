-- Prove2me | Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
-- name    : SingleMachinePrec_IntervalReduction_TreeLayout
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T13:46:05.178992+00:00
-- url     : https://prove2.me/theorems/dcc7561e-b57b-4f6d-a475-01b9cf7c03f6
-- title:
--   Stage 1: a parent-first spanning tree $T$ of $G$ and the gadget graph $G'$ (Section 7)
-- statement:
--   Let $G=(V,E)$ be a graph with vertices $v_1,\dots,v_N$. A **tree layout** of $G$ is a spanning tree $T=(V,E_T)$ with $E_T\subseteq E$, rooted at $v_1$, in which every vertex $v_j$ other than the root has a parent $v_i$ with $i<j$ and $\{v_i,v_j\}\in E$. A breadth-first search tree numbered from the top down and from left to right, as in the paper, is such a layout. The edges of $E\setminus E_T$ are written $\{v_i,v_j\}$ with $i<j$.
--
--   The graph $G'=(V',E')$ is obtained from the tree $T$ as follows.
--
--   1. Keep the vertices $v_i$ and the tree edges $E_T$.
--   2. For each vertex $v_i$ add two new vertices $u^i_2,u^i_1$ and the edges $\{u^i_2,u^i_1\}$ and $\{u^i_1,v_i\}$.
--   3. For each edge $\{v_i,v_j\}\in E\setminus E_T$ with $i<j$ add two new vertices $e^{ij}_1,e^{ij}_2$ and the edges $\{v_i,e^{ij}_1\}$, $\{e^{ij}_1,e^{ij}_2\}$ and $\{e^{ij}_2,u^j_2\}$.
--
--   The edges of $E\setminus E_T$ themselves are not edges of $G'$. Thus $|V'| = 3|V| + 2|E\setminus E_T|$.
--
--   The graph $G'$ is the unweighted vertex cover instance that the scheduling instance of Stage 2 reproduces as the subgraph of $G^S_I$ on its weight-one nodes.
--
--   **Formalization Note** Vertex $v_{i+1}$ is `i : Fin N`; the root is index `0`. The parent function returns `none` exactly at the root. A non-tree edge is a pair `(i, j)` with `i < j`, `G.Adj i j` and `j`'s parent different from `i`. The proof uses only that parents precede children, so the layout is any parent-first spanning tree, which includes the paper's BFS tree.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 662, §7, Stage 1 (tree layout of the graph) and Figure 1

import Mathlib

namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ}

/-- Stage 1 of the proof of Theorem 7.1 (p. 662): a rooted spanning tree `T = (V, E_T)` of a graph
`G` on the vertices `v_1, …, v_N`, with the vertices numbered so that every parent precedes its
children. Vertex `v_{i+1}` is the element `i : Fin N`; the root `s` is `v_1` (index `0`).
`par j = some i` says that `v_{i+1}` is the parent of `v_{j+1}` in `T`; the root has no parent.
A breadth-first search tree numbered from the top down and from left to right is one such
layout. -/
structure TreeLayout (G : SimpleGraph (Fin N)) where
  /-- The parent of each vertex in `T`; `none` exactly at the root. -/
  par : Fin N → Option (Fin N)
  par_eq_none_iff : ∀ j, par j = none ↔ j.val = 0
  /-- Parents are numbered before their children. -/
  par_lt : ∀ j i, par j = some i → i < j
  /-- Tree edges are edges of `G` (`E_T ⊆ E`). -/
  par_adj : ∀ j i, par j = some i → G.Adj i j

variable {G : SimpleGraph (Fin N)}

/-- The edges of `E \ E_T` (p. 662), each written once as `{v_i, v_j}` with `i < j`: an edge of
`G` whose larger endpoint does not have the smaller one as its parent. -/
def NonTreeEdge (L : TreeLayout G) : Type :=
  {q : Fin N × Fin N // q.1 < q.2 ∧ G.Adj q.1 q.2 ∧ L.par q.2 ≠ some q.1}

noncomputable instance NonTreeEdge.instFintype (L : TreeLayout G) : Fintype (NonTreeEdge L) := by
  classical
  exact Subtype.fintype _

instance NonTreeEdge.instDecidableEq (L : TreeLayout G) : DecidableEq (NonTreeEdge L) :=
  inferInstanceAs (DecidableEq {q : Fin N × Fin N // q.1 < q.2 ∧ G.Adj q.1 q.2 ∧ L.par q.2 ≠ some q.1})

/-- The vertices of the graph `G′ = (V′, E′)` of Stage 1 (p. 662): the vertices `v_i` of `T`, two
new vertices `u^i_1, u^i_2` for each vertex `v_i`, and two new vertices `e^{ij}_1, e^{ij}_2` for
each edge `{v_i, v_j} ∈ E \ E_T` with `i < j`. -/
inductive GPVertex (L : TreeLayout G) : Type
  | v (i : Fin N)
  | u1 (i : Fin N)
  | u2 (i : Fin N)
  | e1 (q : NonTreeEdge L)
  | e2 (q : NonTreeEdge L)
  deriving DecidableEq

/-- The edge list of `G′` (p. 662), one orientation per edge: the tree edges `{v_i, v_j} ∈ E_T`,
the edges `{u^i_2, u^i_1}` and `{u^i_1, v_i}`, and for each `{v_i, v_j} ∈ E \ E_T` with `i < j`
the edges `{v_i, e^{ij}_1}`, `{e^{ij}_1, e^{ij}_2}` and `{e^{ij}_2, u^j_2}`. -/
def gpRel (L : TreeLayout G) : GPVertex L → GPVertex L → Prop
  | .v i, .v j => L.par j = some i
  | .u2 i, .u1 j => i = j
  | .u1 i, .v j => i = j
  | .v i, .e1 q => q.1.1 = i
  | .e1 q, .e2 q' => q = q'
  | .e2 q, .u2 j => q.1.2 = j
  | _, _ => False

/-- The graph `G′` of Stage 1 (p. 662), obtained from the tree `T` (not from `G`: the edges of
`E \ E_T` are not edges of `G′`) by attaching the gadgets listed in `gpRel`. -/
def GPrime (L : TreeLayout G) : SimpleGraph (GPVertex L) :=
  SimpleGraph.fromRel (gpRel L)

end SingleMachinePrec.IntervalReduction


