-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_ExtremeBaseVec
-- name    : DiscreteConvex_AlgorithmsB_ExtremeBaseVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:31.317169+00:00
-- url     : https://prove2.me/theorems/74bd536e-e49c-40c1-993e-2035b25d8df6
-- title:
--   ExtremeBaseVec
-- statement:
--   The extreme base $y(v)=\rho(L(v))-\rho(L(v)\setminus\{v\})$ associated with a linear ordering $L$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, Eq. (10.12)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixUpTo
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrefixBefore

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The extreme base `y(v) = ρ(L(v)) - ρ(L(v)∖{v})` associated with a linear ordering `L`
(Eq. (10.12)). -/
def ExtremeBaseVec (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (v : V) : ℤ :=
  rho (PrefixUpTo L v) - rho (PrefixBefore L v)

end DiscreteConvex.AlgorithmsB


