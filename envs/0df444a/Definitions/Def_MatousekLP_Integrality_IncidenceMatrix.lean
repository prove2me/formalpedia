-- Prove2me | Definitions.Def_MatousekLP_Integrality_IncidenceMatrix
-- name    : MatousekLP_Integrality_IncidenceMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:16:43.430136+00:00
-- url     : https://prove2.me/theorems/555c444b-49a0-4be2-9bc0-7b6ea769a7f8
-- title:
--   Vertex–edge incidence matrix of a graph
-- statement:
--   Let $G = (V, E)$ be a simple graph. Its **incidence matrix** $A$ has one row for each vertex and one column for each edge, with entries
--   $$
--   a_{v e} = \begin{cases} 1 & \text{if } v \in e, \\ 0 & \text{otherwise,} \end{cases} \qquad v \in V,\ e \in E .
--   $$
--   Each column therefore contains exactly two ones, at the two end-vertices of the edge.
--
--   The incidence matrix is the constraint matrix of the matching and vertex-cover linear programs of Section 8.2: the row of vertex $v$ gives the constraint $\sum_{e \ni v} x_e \le 1$, and the column of edge $e$ gives $\sum_{v \in e} y_v \ge 1$.
--
--   **Formalization Note** The book numbers the vertices $v_1, \dots, v_n$ and the edges $e_1, \dots, e_m$ and writes $A \in \mathbb{R}^{n \times m}$; here rows are indexed directly by the vertex type $V$ and columns by the edge set of $G$ (a subtype of `Sym2 V`). Total unimodularity does not depend on the order of rows and columns.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 146, §8.2 (Incidence matrices of bipartite graphs)

import Mathlib

namespace MatousekLP.Integrality

/-- The vertex–edge incidence matrix of a simple graph `G` (p. 146): rows are indexed by
the vertices, columns by the edges of `G`, and the entry in row `v`, column `e` is `1`
if `v ∈ e` and `0` otherwise. -/
def incidenceMatrix {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    Matrix V G.edgeSet ℝ :=
  Matrix.of fun v e => if v ∈ (e : Sym2 V) then 1 else 0

end MatousekLP.Integrality


