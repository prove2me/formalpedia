-- Prove2me | Definitions.Def_CombOpt_MatroidPolytope_Graph_IsMatching
-- name    : CombOpt_MatroidPolytope_Graph_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:07:37.343521+00:00
-- url     : https://prove2.me/theorems/431f7167-ae28-45dd-a0a0-887f46948f13
-- title:
--   Matching in a graph
-- statement:
--   A **matching** in a graph $G=(V,E)$ is a set $M$ of edges such that no node of $G$ is incident with more than one edge of $M$; it covers exactly $2|M|$ nodes, so it contains no loops.
--
--   **Formalization Note** Stated as: no edge of $M$ is a loop, and two distinct edges of $M$ have no common end.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_Graph

namespace CombOpt.MatroidPolytope

/-- **Matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A matching in a graph G = (V, E) is a set M of edges such that
no node of G is incident with more than one edge in M. … Note that the number of nodes covered by
M is exactly 2|M|".

`G.IsMatching M` says that no edge of `M` is a loop and that two distinct edges of `M` have no
common end.

**Formalization Note.** The book's remark that a matching covers exactly `2|M|` nodes excludes
loops from matchings; the loop exclusion is written out. -/
def Graph.IsMatching {V E : Type*} (G : Graph V E) (M : Finset E) : Prop :=
  (∀ e ∈ M, ¬ (G.ends e).IsDiag) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : V, v ∈ G.ends e → v ∉ G.ends f

end CombOpt.MatroidPolytope


