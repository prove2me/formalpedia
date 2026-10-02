-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_WalkLength
-- name    : DiscreteConvex_LConvexSetsB_WalkLength
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:45.079064+00:00
-- url     : https://prove2.me/theorems/70bf69ca-0718-48ad-addc-2d10caeb502d
-- title:
--   WalkLength
-- statement:
--   The **length** of a walk $w : \{0,\ldots,k\} \to V$ with respect to a distance function $\gamma$: the sum of $\gamma$ over its consecutive edges.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122 (supporting the shortest-path closure $\\bar\\gamma$).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122 (supporting the shortest-path closure $\\bar\\gamma$)

import Mathlib

/-!
The length of a walk with respect to a distance function, supporting the shortest-path
closure `γ̄` used in Proposition 5.1 (Murota, *Discrete Convex Analysis*, SIAM 2003,
p.122), in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The **length** of a walk `w : Fin (k+1) → V` (vertices `w(0), …, w(k)`) with respect to
a distance function `γ`: the sum of `γ` over its consecutive edges. -/
def WalkLength {V : Type*} (γ : V → V → WithTop ℝ) (k : ℕ) (w : Fin (k + 1) → V) : WithTop ℝ :=
  ∑ i : Fin k, γ (w i.castSucc) (w i.succ)

end DiscreteConvex.LConvexSetsB


