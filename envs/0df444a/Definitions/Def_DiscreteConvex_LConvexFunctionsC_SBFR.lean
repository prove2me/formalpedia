-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
-- name    : DiscreteConvex_LConvexFunctionsC_SBFR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:32:00.39198+00:00
-- url     : https://prove2.me/theorems/c34d9a34-4000-4e6c-ae24-196021e5018e
-- title:
--   SBFR
-- statement:
--   Axiom (SBF[R]): submodularity of a polyhedral convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, axiom (SBF[R])

import Mathlib

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[R]): submodularity of a polyhedral convex function. -/
def SBFR (g : (V → ℝ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.LConvexFunctionsC


