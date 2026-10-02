-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConcaveF
-- name    : DiscreteConvex_IntegralConvexityB_IsClosedConcaveF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:03:51.447276+00:00
-- url     : https://prove2.me/theorems/3c10277d-640d-42b5-888a-04c4a1ca76da
-- title:
--   Closed concave function
-- statement:
--   Concave with closed hypograph.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, footnote 37.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.105, footnote 37

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConcaveF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Hypo

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.105, footnote 37 ("f and -h are closed convex
functions"): a closed concave function, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `h` is **closed concave** if `hyp h` is a closed convex set (matching footnote 37's "`-h`
closed convex" via the hypograph, dual to `IsClosedConvexF`). -/
def IsClosedConcaveF {V : Type*} [Fintype V] (h : (V → ℝ) → EReal) : Prop :=
  IsConcaveF h ∧ IsClosed (Hypo h)

end DiscreteConvex.IntegralConvexityB


