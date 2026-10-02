-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_SeparablePerturbR
-- name    : DiscreteConvex_MConvexFunctionsD_SeparablePerturbR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:48:55.145579+00:00
-- url     : https://prove2.me/theorems/b9101fb8-ba8f-40cb-8880-24f76b751d98
-- title:
--   SeparablePerturbR
-- statement:
--   The separable perturbation $\tilde f(x)=f(x)+\sum_v\phi_v(x(v))$ for real-domain $f$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.79).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.163, Eq. (6.79)

import Mathlib

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The separable perturbation `f̃(x) = f(x) + Σᵥ ϕᵥ(x(v))` for real-domain `f`. -/
def SeparablePerturbR (f : (V → ℝ) → WithTop ℝ) (phi : V → ℝ → WithTop ℝ) : (V → ℝ) → WithTop ℝ :=
  fun x => f x + ∑ v, phi v (x v)

end DiscreteConvex.MConvexFunctionsD


