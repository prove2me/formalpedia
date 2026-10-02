-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
-- name    : DiscreteConvex_IntegralConvexityB_IsPerfectMatchingBij
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:56.681412+00:00
-- url     : https://prove2.me/theorems/2c46052e-1902-4061-a20f-2aa2c39f7d09
-- title:
--   Perfect matching as a bijection
-- statement:
--   A perfect matching of a bipartite graph, as a bijection $\sigma$ between the two sides with $(u,\sigma u)\in E$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.109

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.109: a perfect matching of a bipartite graph,
represented as a bijection between the two sides, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- A **perfect matching** of the bipartite graph `(Vp, Vm; E)`, represented as a bijection
`σ : Vp ≃ Vm` all of whose pairs `(u, σ u)` are arcs of `E`. -/
def IsPerfectMatchingBij {Vp Vm : Type*} (E : Set (Vp × Vm)) (sigma : Vp ≃ Vm) : Prop :=
  ∀ u, (u, sigma u) ∈ E

end DiscreteConvex.IntegralConvexityB


