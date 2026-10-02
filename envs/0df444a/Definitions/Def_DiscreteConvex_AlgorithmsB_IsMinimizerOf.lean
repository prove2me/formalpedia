-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_IsMinimizerOf
-- name    : DiscreteConvex_AlgorithmsB_IsMinimizerOf
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:49:50.272806+00:00
-- url     : https://prove2.me/theorems/7b6d843c-757f-48de-b35a-c6f69e16c711
-- title:
--   IsMinimizerOf
-- statement:
--   $X$ minimizes $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.289, adjacent to Eq. (10.11)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `X` minimizes `ρ`. -/
def IsMinimizerOf (rho : Finset V → ℤ) (W : Finset V) : Prop := ∀ X, rho W ≤ rho X

end DiscreteConvex.AlgorithmsB


