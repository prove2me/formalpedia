-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsSteepestPair
-- name    : DiscreteConvex_Algorithms_IsSteepestPair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:13.911823+00:00
-- url     : https://prove2.me/theorems/17c919b1-0490-41aa-a846-f54e0f51f76d
-- title:
--   Steepest pair at a point (step S1, p.282)
-- statement:
--   $(u,v)$ is a **steepest pair** at $x$ for $f$ (step S1 of the steepest descent algorithm): $u \ne v$ and $(u,v)$ minimizes $f(x - \chi_u + \chi_v)$ over all $u' \ne v'$ in $V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.282

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec

open DiscreteConvex.MConvexFunctions

namespace DiscreteConvex.Algorithms

/-- `(u,v)` is a **steepest pair** at `x` for `f` (step S1 of the steepest descent algorithm,
p.282): `u ≠ v` and `(u,v)` minimizes `f(x - χ_u + χ_v)` over all `u' ≠ v'` in `V`. -/
def IsSteepestPair {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (x : V → ℤ) (u v : V) : Prop :=
  u ≠ v ∧ ∀ u' v' : V, u' ≠ v' →
    f (fun w => x w - CharVec u w + CharVec v w) ≤ f (fun w => x w - CharVec u' w + CharVec v' w)

end DiscreteConvex.Algorithms


