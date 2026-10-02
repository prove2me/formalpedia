-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsSteepestDescentTerminal
-- name    : DiscreteConvex_Algorithms_IsSteepestDescentTerminal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:46.158463+00:00
-- url     : https://prove2.me/theorems/c9469fba-0a67-45b5-96ee-8db1c2877d9d
-- title:
--   Termination test for steepest descent (step S2, p.282)
-- statement:
--   The steepest descent algorithm's stopping test (step S2): $x$ is **terminal** for $f$ if no swap $x - \chi_u + \chi_v$ ($u \ne v$) improves on $f(x)$ — by Theorem 6.26 (the M-optimality criterion), this is exactly global minimality.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- The steepest descent algorithm's stopping test (step S2, p.282): `x` is terminal for `f`
if no swap `x - χ_u + χ_v` (`u ≠ v`) improves on `f(x)`. -/
def IsSteepestDescentTerminal {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) : Prop :=
  ∀ u v : V, u ≠ v → f x ≤ f (fun w => x w - CharVec u w + CharVec v w)

end DiscreteConvex.Algorithms


