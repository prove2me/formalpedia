-- Prove2me | Definitions.Def_GeometryOfGraphs_Cube_Implements
-- name    : GeometryOfGraphs_Cube_Implements
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:54.228135+00:00
-- url     : https://prove2.me/theorems/7f2cbf86-80cc-4d01-a7fd-ef8cf3982e85
-- title:
--   Matrix implementing a graph metric
-- statement:
--   Let $G$ be a graph with vertex set $V$ and graph distance $d_G$. A real matrix $M$, with rows indexed by $V$ and any finite number $r$ of columns, implements $G$ when every pair of rows is separated by exactly its graph distance in the maximum norm:
--
--   $$
--   \max_{1\le k\le r}|M_{ik}-M_{jk}|=d_G(i,j).
--   $$
--
--   Implementing matrices connect isometric dimension with matrix rank in Theorem 5.7.
--
--   **Formalization Note** Lean states that every coordinate difference is at most $d_G(i,j)$ and, for distinct rows, one coordinate attains that distance. This also handles the one-vertex case with zero columns.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 232, Section 5.3, definition preceding Theorem 5.7; https://doi.org/10.1007/BF01200757

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.Cube

/-- A matrix whose row distances in the maximum norm equal the graph distances. -/
def Implements {V : Type*} (G : SimpleGraph V) {r : ℕ}
    (M : Matrix V (Fin r) ℝ) : Prop :=
  ∀ i j,
    (∀ k, |M i k - M j k| ≤ (G.dist i j : ℝ)) ∧
    (i ≠ j → ∃ k, |M i k - M j k| = (G.dist i j : ℝ))

end GeometryOfGraphs.Cube


