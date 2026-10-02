-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SBFR
-- name    : DiscreteConvex_LConvexFunctionsD_SBFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:14.302143+00:00
-- url     : https://prove2.me/theorems/8d94b7b0-18a1-4d12-8568-44633c07c806
-- title:
--   SBFR
-- statement:
--   Axiom (SBF[R]): submodularity of a polyhedral convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[R]): submodularity of a polyhedral convex function. -/
def SBFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.LConvexFunctionsD


