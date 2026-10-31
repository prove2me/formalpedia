-- Prove2me | Definitions.Def_CombOpt_TutteBerge_Multigraph_IsMatching
-- name    : CombOpt_TutteBerge_Multigraph_IsMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:02.297852+00:00
-- url     : https://prove2.me/theorems/57fab8c3-ebcd-4187-b940-3a05d8c3a429
-- title:
--   Matching
-- statement:
--   A **matching** of $G$ is a set $M\subseteq E$ of non-loop edges such that no node of $G$ is incident with more than one edge of $M$.
--
--   **Formalization Note** The book's sentence does not exclude loops, but it states right afterwards that $M$ covers exactly $2|M|$ nodes, which forces $M$ to contain no loop. The exclusion is the first clause of the definition.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §5.1, p. 127 (PDF p. 135)

import Mathlib
import Definitions.Def_CombOpt_TutteBerge_Multigraph

namespace CombOpt.TutteBerge

/-- **A matching.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §5.1, p. 127 (PDF p. 135): "A *matching* in a graph G = (V, E) is a set M of edges such that
no node of G is incident with more than one edge in M."

**Formalization Note.** A matching contains no loop. The sentence quoted above does not say so, but
the next lines of the book do: "the number of nodes covered by M is exactly 2|M|" and "the number
of M-exposed nodes is |V| − 2|M|", which fail for a matching containing a loop. This is the first
clause below. The second clause says that two edges of `M` sharing an end are equal. -/
def Multigraph.IsMatching {V E : Type*} (G : Multigraph V E) (M : Set E) : Prop :=
  (∀ e ∈ M, ¬ (G.ends e).IsDiag) ∧
    ∀ e ∈ M, ∀ f ∈ M, ∀ v : V, v ∈ G.ends e → v ∈ G.ends f → e = f

end CombOpt.TutteBerge


