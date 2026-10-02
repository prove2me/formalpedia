-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_CharVec
-- name    : DiscreteConvex_CombinatorialC_CharVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:39:11.02693+00:00
-- url     : https://prove2.me/theorems/fede8471-6fba-4ae9-8f23-4974bd6872e0
-- title:
--   Unit (characteristic) vector
-- statement:
--   The unit vector $\chi_i$: $1$ at coordinate $i$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, citing Eq. (1.19)-style notation: the unit
(characteristic) vector, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The unit vector `χ_i : W → ℝ`, `1` at `i` and `0` elsewhere. -/
def CharVec {W : Type*} [DecidableEq W] (i : W) : W → ℝ :=
  fun j => if j = i then 1 else 0

end DiscreteConvex.CombinatorialC


