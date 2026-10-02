-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_DistanceFunction
-- name    : DiscreteConvex_LConvexSetsB_DistanceFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:22.279698+00:00
-- url     : https://prove2.me/theorems/dd692ede-6a1a-4c20-b496-4c2dc2d3344c
-- title:
--   DistanceFunction
-- statement:
--   A **distance function** $\gamma : V \times V \to \mathbb R \cup \{+\infty\}$ with $\gamma(v,v)=0$; $\gamma$ may take negative finite values and need not be symmetric.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122: distance functions, in
`DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- A **distance function** `γ : V × V → R ∪ {+∞}` with `γ(v,v) = 0`; `γ` may take
negative finite values and need not be symmetric. -/
def DistanceFunction {V : Type*} (γ : V → V → WithTop ℝ) : Prop := ∀ v, γ v v = 0

end DiscreteConvex.LConvexSetsB


