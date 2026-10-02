-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOf
-- name    : DiscreteConvex_AlgorithmsC_IsMinimizerOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:17:15.160668+00:00
-- url     : https://prove2.me/theorems/cbb6abf4-bd97-4746-8dec-dcbb83367ff9
-- title:
--   IsMinimizerOf
-- statement:
--   $X$ minimizes $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `X` minimizes `ρ`. -/
def IsMinimizerOf (rho : Finset V → ℤ) (W : Finset V) : Prop := ∀ X, rho W ≤ rho X

end DiscreteConvex.AlgorithmsC


