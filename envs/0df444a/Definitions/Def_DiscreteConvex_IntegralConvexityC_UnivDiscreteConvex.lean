-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_UnivDiscreteConvex
-- name    : DiscreteConvex_IntegralConvexityC_UnivDiscreteConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:16.633994+00:00
-- url     : https://prove2.me/theorems/849eea69-3d14-4f11-9017-173dff9c2ad9
-- title:
--   Univariate discrete convex function class C[Z to R]
-- statement:
--   $\phi(t-1)+\phi(t+1)\ge2\phi(t)$, $\operatorname{dom}\phi\ne\emptyset$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Eq. (3.68).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Eq. (3.68)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Eq. (3.68): the class `C[Z→R]` of
univariate discrete convex functions, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `φ ∈ C[Z→R]` (Eq. (3.68)): `dom_Z φ ≠ ∅` and `φ(t-1) + φ(t+1) ≥ 2φ(t)` for all `t`
(written `φ(t)+φ(t)` to avoid scalar multiplication on `WithTop ℝ`). -/
def UnivDiscreteConvex (phi : ℤ → WithTop ℝ) : Prop :=
  (∃ t, phi t ≠ ⊤) ∧ ∀ t : ℤ, phi (t - 1) + phi (t + 1) ≥ phi t + phi t

end DiscreteConvex.IntegralConvexityC


