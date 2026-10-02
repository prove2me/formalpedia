-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
-- name    : DiscreteConvex_CombinatorialB_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:31:11.189009+00:00
-- url     : https://prove2.me/theorems/66aceb90-4871-4be3-bbec-df4d09c787b3
-- title:
--   Unit (characteristic) vector
-- statement:
--   The unit vector $\chi_i \in \mathbb R^V$: $1$ at coordinate $i$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, citing Eq. (1.19)-style notation: the
`i`-th unit (characteristic) vector `χ_i ∈ Rⱽ`, in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- The unit vector `χ_i : V → ℝ`, `1` at `i` and `0` elsewhere. -/
def CharVec {V : Type*} [DecidableEq V] (i : V) : V → ℝ :=
  fun j => if j = i then 1 else 0

end DiscreteConvex.CombinatorialB


