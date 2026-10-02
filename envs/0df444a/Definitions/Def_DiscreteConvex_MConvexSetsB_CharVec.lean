-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
-- name    : DiscreteConvex_MConvexSetsB_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:25:49.879417+00:00
-- url     : https://prove2.me/theorems/c388c2e1-277e-4479-b467-7d9318c9d7b0
-- title:
--   CharVec
-- statement:
--   The **characteristic vector** $\chi_u \in \mathbb Z^V$ of $u \in V$: $1$ at $u$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101: the characteristic vector `χ_u` of a
single ground-set element, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The characteristic vector `χ_u ∈ Zⱽ` of `u ∈ V`: `1` at `u`, `0` elsewhere. -/
def CharVec {V : Type*} [DecidableEq V] (u : V) : V → ℤ :=
  fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexSetsB


