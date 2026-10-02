-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_SeparablePerturb
-- name    : DiscreteConvex_MConvexFunctionsB_SeparablePerturb
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:06:37.682722+00:00
-- url     : https://prove2.me/theorems/4a8fa23a-7c10-43a6-aac0-0f9f84606a42
-- title:
--   SeparablePerturb
-- statement:
--   The separable perturbation $\tilde f(x) = f(x) + \sum_v \phi_v(x(v))$, Eq. (6.46).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.46).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.143, Eq. (6.46)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.143, Eq. (6.46), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The separable perturbation `f̃(x) = f(x) + Σᵥ ϕᵥ(x(v))`, Eq. (6.46). -/
def SeparablePerturb {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ) (phi : V → ℤ → WithTop ℝ) :
    (V → ℤ) → WithTop ℝ :=
  fun x => f x + ∑ v, phi v (x v)

end DiscreteConvex.MConvexFunctionsB


