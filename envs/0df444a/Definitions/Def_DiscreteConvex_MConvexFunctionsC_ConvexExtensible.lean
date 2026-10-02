-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
-- name    : DiscreteConvex_MConvexFunctionsC_ConvexExtensible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:37:34.924969+00:00
-- url     : https://prove2.me/theorems/c363c20d-6d5c-4f20-afb6-8370c7578996
-- title:
--   ConvexExtensible
-- statement:
--   $f$ is **convex extensible**: its convex closure agrees with $f$ itself on $\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `f` is convex extensible, Eq. (3.57): its convex closure agrees with `f` on `Zⱽ`. -/
def ConvexExtensible (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, ConvexClosureVal f (fun v => (x v : ℝ)) = f x

end DiscreteConvex.MConvexFunctionsC


