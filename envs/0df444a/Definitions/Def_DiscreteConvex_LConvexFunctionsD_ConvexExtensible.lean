-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexExtensible
-- name    : DiscreteConvex_LConvexFunctionsD_ConvexExtensible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:05:10.315036+00:00
-- url     : https://prove2.me/theorems/6ff41986-6894-45e2-abc4-843ee15450f3
-- title:
--   ConvexExtensible
-- statement:
--   $g$ is convex extensible: its convex closure agrees with $g$ on $\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `g` is convex extensible: its convex closure agrees with `g` on `Zⱽ`. -/
def ConvexExtensible (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x : V → ℤ, ConvexClosureVal g (fun v => (x v : ℝ)) = g x

end DiscreteConvex.LConvexFunctionsD


