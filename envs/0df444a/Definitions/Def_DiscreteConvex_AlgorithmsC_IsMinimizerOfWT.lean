-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOfWT
-- name    : DiscreteConvex_AlgorithmsC_IsMinimizerOfWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:38.807321+00:00
-- url     : https://prove2.me/theorems/64467c7e-4afc-4310-b145-3a31bdcb4dd1
-- title:
--   IsMinimizerOfWT
-- statement:
--   $X$ minimizes the $\mathbb R\cup\{+\infty\}$-valued set function $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.305, adjacent to Eq. (10.32).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.305, adjacent to Eq. (10.32)

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `X` minimizes the `WithTop ℝ`-valued set function `ρ`. -/
def IsMinimizerOfWT (rho : Finset V → WithTop ℝ) (W : Finset V) : Prop := ∀ X, rho W ≤ rho X

end DiscreteConvex.AlgorithmsC


