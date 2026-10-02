-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_DistanceFunction
-- name    : DiscreteConvex_LConvexSets_DistanceFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:35:05.30978+00:00
-- url     : https://prove2.me/theorems/7c7654c2-54ad-4976-97d2-14caa17ede25
-- title:
--   Distance function on a finite ground set
-- statement:
--   A **distance function** $\gamma : V \times V \to \mathbb R \cup \{+\infty\}$ (may take negative finite values, need not be symmetric): $\gamma(v,v) = 0$ for every $v \in V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122: distance functions, in
`DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- A **distance function** `γ : V × V → R ∪ {+∞}` (may take negative finite values, need not
be symmetric): `γ(v,v) = 0` for every `v ∈ V`. -/
def DistanceFunction {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ v : V, γ v v = 0

end DiscreteConvex.LConvexSets


