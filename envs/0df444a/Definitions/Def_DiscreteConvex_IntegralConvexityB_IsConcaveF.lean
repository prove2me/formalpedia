-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConcaveF
-- name    : DiscreteConvex_IntegralConvexityB_IsConcaveF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:16.160809+00:00
-- url     : https://prove2.me/theorems/839d9f8f-ec19-4c81-bfa3-64261809077e
-- title:
--   Concavity of a function via its hypograph
-- statement:
--   $h$ concave iff $\operatorname{hyp}h$ is a convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.6)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Hypo

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, Eq. (3.6): concavity of a function via its
hypograph, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `h` is concave iff `hyp h` is a convex set, the epigraph-style characterization dual to
`IsConvexF`. -/
def IsConcaveF {V : Type*} [Fintype V] (h : (V → ℝ) → EReal) : Prop :=
  Convex ℝ (Hypo h)

end DiscreteConvex.IntegralConvexityB


