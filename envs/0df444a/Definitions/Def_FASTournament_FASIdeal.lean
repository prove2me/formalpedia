-- Prove2me | Definitions.Def_FASTournament_FASIdeal
-- name    : FASTournament_FASIdeal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:24.181322+00:00
-- url     : https://prove2.me/theorems/97e44c39-df2e-428c-bc20-d9b091182bc9
-- title:
--   FAS ideal (FASI) digraph
-- statement:
--   A digraph $G=(V,A)$ is **FAS ideal (FASI)** if
--   $$
--   \{x\in\mathbb R^A : Nx\ge\mathbf 1,\ x\ge\mathbf 0\}=\Big\{x\ge 0 : \sum_{e\in F}x(e)\ge 1 \text{ for every FAS } F\Big\}
--   $$
--   is an integral polyhedron, i.e. the convex hull of the integral vectors it contains.
--
--   **Formalization Note** Integrality is the published definition `DiscreteConvex.MConvexSets.IsIntegralPolyhedron`. If $G$ is acyclic, $\emptyset$ is an FAS and the polyhedron is empty, hence integral.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsFAS
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegralPolyhedron

namespace FASTournament

/-- **FAS ideal (FASI) digraph.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3: "We say that G is FAS ideal (FASI) if Nx ≥ 1, x ≥ 0 defines an integral
polyhedron".

`G` is FAS ideal if the polyhedron `{x ∈ ℝ^A : x ≥ 0, x(F) ≥ 1 for every FAS F}` is the convex
hull of the integral vectors it contains (p.2).

**Formalization Note.** Integrality is the published
`DiscreteConvex.MConvexSets.IsIntegralPolyhedron` (`P = conv(P ∩ ℤ^A)`). Rows are all FASs;
restricting to minimal FASs gives the same set. If `G` is acyclic the polyhedron is empty, which
is integral. -/
def FASIdeal {V : Type*} (G : Digraph V) : Prop :=
  DiscreteConvex.MConvexSets.IsIntegralPolyhedron
    {x : Arc G → ℝ | (∀ e, 0 ≤ x e) ∧ ∀ F : Finset (Arc G), IsFAS G F → 1 ≤ ∑ e ∈ F, x e}

end FASTournament


