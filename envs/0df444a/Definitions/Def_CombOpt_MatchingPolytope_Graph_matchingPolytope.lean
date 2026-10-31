-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_matchingPolytope
-- name    : CombOpt_MatchingPolytope_Graph_matchingPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:23.135961+00:00
-- url     : https://prove2.me/theorems/efcbd6a7-ac1f-4d8c-8f9a-4fce2d1fa292
-- title:
--   The matching polytope $M(G)$
-- statement:
--   The **matching polytope** of a graph $G=(V,E)$ is the convex hull of the characteristic vectors of the matchings of $G$:
--   $$M(G)=\operatorname{conv.hull}\{\chi_M:\ M \text{ a matching of } G\}\subseteq\mathbb R^E.$$
--
--   Theorem 6.20 (Edmonds) describes $M(G)$ by the linear system (6.7).
--
--   **Formalization Note** Mathlib's `convexHull ℝ` is used; for this finite set of points it is the set of convex combinations, the book's conv.hull.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 214 (PDF p. 222)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsMatching
import Definitions.Def_CombOpt_MatchingPolytope_charVec

namespace CombOpt.MatchingPolytope

/-- **The matching polytope M(G).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 214 (PDF p. 222): "The matching polytope of a graph G (denoted by M(G)) is the
convex hull of the (characteristic vectors of) matchings of G."

**Formalization Note.** `convexHull ℝ` is Mathlib's convex hull, the set of all convex
combinations of finitely many points of the set; for the finite set of characteristic vectors of
matchings it is the book's `conv.hull` (p. 199: the set of all vectors that can be written as a
convex combination of the set). -/
noncomputable def Graph.matchingPolytope {V E : Type*} [Fintype E] (G : Graph V E) :
    Set (E → ℝ) :=
  convexHull ℝ {x | ∃ M : Finset E, G.IsMatching M ∧ x = charVec M}

end CombOpt.MatchingPolytope


