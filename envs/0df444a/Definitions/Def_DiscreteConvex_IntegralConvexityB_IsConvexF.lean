-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConvexF
-- name    : DiscreteConvex_IntegralConvexityB_IsConvexF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:18.329206+00:00
-- url     : https://prove2.me/theorems/4a7e14ab-eec6-4b22-99c2-023fac7b739e
-- title:
--   Convexity of a function via its epigraph
-- statement:
--   $f$ convex iff $\operatorname{epi}f$ is a convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.15).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.15)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79, Eq. (3.15): convexity of a function via
its epigraph, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` is convex iff `epi f` is a convex set (Eq. (3.15)), the equivalent characterization the
book gives to (3.4). -/
def IsConvexF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  Convex ℝ (Epi f)

end DiscreteConvex.IntegralConvexityB


