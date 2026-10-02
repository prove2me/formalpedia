-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
-- name    : DiscreteConvex_LConvexFunctionsB_TRF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:20:36.549271+00:00
-- url     : https://prove2.me/theorems/c3c15b09-4075-445c-a4ef-1c148bf7353f
-- title:
--   TRF
-- statement:
--   Axiom (TRF[Z]): $\exists r$, $g(p+\mathbf 1)=g(p)+r$. A function satisfying (SBF[Z]) and (TRF[Z]), with nonempty domain, is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (TRF[Z])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (TRF[Z]): `∃r, g(p+1) = g(p)+r`. A function satisfying (SBF[Z]) and (TRF[Z]), with
nonempty domain, is L-convex. -/
def TRF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∃ r : ℝ, ∀ p : V → ℤ, g (p + 1) = g p + (r : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsB


