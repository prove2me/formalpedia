-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
-- name    : DiscreteConvex_MConvexFunctions_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:37.872667+00:00
-- url     : https://prove2.me/theorems/808fb63c-0cd4-4c6b-b488-704e1569fb01
-- title:
--   Characteristic vector of a ground-set element
-- statement:
--   The characteristic vector $\chi_u \in \mathbb Z^V$ of $u \in V$: $1$ at $u$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.133-135.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.133-135

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133-135: the characteristic vector of a
single ground-set element, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The characteristic vector `χ_u ∈ Zⱽ` of `u ∈ V`: `1` at `u`, `0` elsewhere. -/
def CharVec {V : Type*} [DecidableEq V] (u : V) : V → ℤ :=
  fun v => if v = u then 1 else 0

end DiscreteConvex.MConvexFunctions


