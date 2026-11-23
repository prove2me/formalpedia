-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_extendedDoubleCover
-- name    : AlonMilman_PropertyT_Supplement_extendedDoubleCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:26:58.060863+00:00
-- url     : https://prove2.me/theorems/04b66e7c-c956-484a-8331-f4e963a9b3ed
-- title:
--   Definition 4.2 — the extended double cover of a graph
-- statement:
--   Let $G = (V, E)$ be a graph on the vertex set $V = \{v_1, \dots, v_n\}$, possibly with parallel edges and loops. The **extended double cover** of $G$ is the bipartite graph $H$ on the set of inputs $X = \{x_1, \dots, x_n\}$ and outputs $Y = \{y_1, \dots, y_n\}$ in which $x_i \in X$ and $y_j \in Y$ are adjacent iff
--
--   $$i = j \quad\text{or}\quad v_i v_j \in E.$$
--
--   So $H$ contains the perfect matching $x_i y_i$ together with two edges $x_i y_j$, $x_j y_i$ for every edge $v_i v_j$ of $G$. By Theorem 4.3 it is an expander whenever $G$ is an enlarger.
--
--   **Formalization Note** $G$ is given by its multiplicity matrix $M$ (as in the published definition of an enlarger) and $v_i v_j \in E$ means $M_{v_i v_j} > 0$, so parallel edges give a single edge of $H$. Inputs and outputs are both copies of $V$, and $H$ is returned as its edge set, a set of (input, output) pairs.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 83, Definition 4.2

import Mathlib

namespace AlonMilman.PropertyT.Supplement

/-- The extended double cover of a finite (multi)graph `G` on the vertex set `V`, given by its
multiplicity matrix `M : Matrix V V ℕ` (Alon–Milman 1985, Definition 4.2, p. 83). It is the
bipartite graph with inputs `X = {x_v : v ∈ V}` and outputs `Y = {y_w : w ∈ V}` — both copies of
`V` — in which `x_v` and `y_w` are adjacent iff `v = w` or `G` has an edge between `v` and `w`
(`M v w > 0`). It is returned as its edge set, a finset of (input, output) pairs; parallel edges
of `G` give one edge of the cover. -/
def extendedDoubleCover {V : Type} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) :
    Finset (V × V) :=
  Finset.univ.filter (fun p => p.1 = p.2 ∨ 0 < M p.1 p.2)

end AlonMilman.PropertyT.Supplement


