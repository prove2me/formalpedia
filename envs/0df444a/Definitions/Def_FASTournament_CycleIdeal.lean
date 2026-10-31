-- Prove2me | Definitions.Def_FASTournament_CycleIdeal
-- name    : FASTournament_CycleIdeal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:13.323118+00:00
-- url     : https://prove2.me/theorems/61b41846-4fa7-4468-a368-13951d6f1bd8
-- title:
--   Cycle ideal (CI) digraph
-- statement:
--   A digraph $G=(V,A)$ is **cycle ideal (CI)** if the polyhedron
--   $$
--   P=\Big\{x\in\mathbb R^A : x\ge 0,\ \sum_{e\in C}x(e)\ge 1 \text{ for every directed cycle } C\Big\}
--   $$
--   defined by $\pi(G)$ is integral, i.e. the convex hull of the integral vectors it contains.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsDirCycle
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegralPolyhedron

namespace FASTournament

/-- **Cycle ideal (CI) digraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2: "let P denote the polyhedron defined by π(G). We call P integral if it is the convex
hull of all integral vectors contained in P. … We say that G is cycle ideal (CI) if P is an
integral polyhedron".

`P = {x ∈ ℝ^A : x ≥ 0, x(C) ≥ 1 for every directed cycle C}`.

**Formalization Note.** Integrality is the published
`DiscreteConvex.MConvexSets.IsIntegralPolyhedron`. -/
def CycleIdeal {V : Type*} (G : Digraph V) : Prop :=
  DiscreteConvex.MConvexSets.IsIntegralPolyhedron
    {x : Arc G → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ C : Finset (Arc G), IsDirCycle G C → 1 ≤ ∑ e ∈ C, x e}

end FASTournament


