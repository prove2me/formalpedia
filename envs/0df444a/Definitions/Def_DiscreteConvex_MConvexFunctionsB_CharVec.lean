-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
-- name    : DiscreteConvex_MConvexFunctionsB_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:05:26.869777+00:00
-- url     : https://prove2.me/theorems/c7d6ba06-9fed-4354-ab62-6460801ca8ef
-- title:
--   CharVec
-- statement:
--   The characteristic vector $\chi_u \in \mathbb Z^V$ of $u \in V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133-135.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133-135

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133-135, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- The characteristic vector `χ_u ∈ Zⱽ` of `u ∈ V`. -/
def CharVec {V : Type*} [DecidableEq V] (u : V) : V → ℤ := fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctionsB


