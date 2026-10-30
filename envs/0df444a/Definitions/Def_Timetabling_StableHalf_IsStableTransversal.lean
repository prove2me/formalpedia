-- Prove2me | Definitions.Def_Timetabling_StableHalf_IsStableTransversal
-- name    : Timetabling_StableHalf_IsStableTransversal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:27:07.621155+00:00
-- url     : https://prove2.me/theorems/aa98e89b-1dff-4e3d-bead-a0014836cbd0
-- title:
--   Stable transversal of the pairs $\{x_j, \bar x_j\}$
-- statement:
--   Let $G$ be a simple graph on the $2n$ nodes $x_1, \bar x_1, \dots, x_n, \bar x_n$; the pairs $\{x_j, \bar x_j\}$ form a perfect matching. A **choice** $c$ picks one node of every pair: $x_j$ if $c_j = \text{true}$ and $\bar x_j$ if $c_j = \text{false}$. The choice is a **stable transversal** of $G$ when the picked nodes are pairwise non-adjacent:
--
--   $$
--   \{\, (j, c_j) : j = 1, \dots, n \,\} \ \text{is an independent (stable) set of } G .
--   $$
--
--   When every $x_j$ is linked to $\bar x_j$, the stable sets of $n$ nodes are exactly the ranges of the stable transversals; this is how a timetable becomes a choice of one schedule per teacher in the proof of Proposition 2.4.
--
--   **Formalization Note** Nodes are `Fin n × Bool`, with `(j, true)` $= x_j$ and `(j, false)` $= \bar x_j$, indices 0-based. Stability is Mathlib's `SimpleGraph.IsIndepSet` of the range of `j ↦ (j, c j)`.
-- source:
--   de Werra (1985), proof of Proposition 2.4, p. 155, "(in particular, nodes x_j and x̄_j are linked)" and "a set of n pairwise non adjacent nodes". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib

namespace Timetabling.StableHalf

/-- **A stable set choosing one node of every matched pair.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4 and Remark,
p. 155: nodes `x_j`, `x̄_j` for teacher `t_j` are linked, and a timetable is "a set of n pairwise
non adjacent nodes".

The vertices are `Fin n × Bool`: `(j, true)` is `x_j` and `(j, false)` is `x̄_j`. A choice
`c : Fin n → Bool` picks the node `(j, c j)` of every pair `j`; it is a *stable transversal* of
`G` when the picked nodes are pairwise non-adjacent.

**Formalization Note.** Indices are 0-based (`Fin n`). Under the hypothesis that every pair
`(j, true)`, `(j, false)` is an edge, the stable sets of `n` nodes are exactly the ranges of the
stable transversals (milestone `stable_nset_iff_transversal`). -/
def IsStableTransversal {n : ℕ} (G : SimpleGraph (Fin n × Bool)) (c : Fin n → Bool) : Prop :=
  G.IsIndepSet (Set.range fun j => (j, c j))

end Timetabling.StableHalf


