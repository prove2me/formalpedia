-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexExtensible
-- name    : DiscreteConvex_LConvexFunctionsC_ConvexExtensible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:49:15.473346+00:00
-- url     : https://prove2.me/theorems/3eda46ba-e530-4d10-8c47-4606b87b7e06
-- title:
--   ConvexExtensible
-- statement:
--   $g$ is convex extensible: its convex closure agrees with $g$ on $\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ConvexClosureVal

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is convex extensible: its convex closure agrees with `g` on `Zⱽ`, Eq. (3.57). -/
def ConvexExtensible (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, ConvexClosureVal g (fun v => (x v : ℝ)) = g x

end DiscreteConvex.LConvexFunctionsC


