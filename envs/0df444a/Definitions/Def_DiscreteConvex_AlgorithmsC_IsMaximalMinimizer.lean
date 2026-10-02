-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_IsMaximalMinimizer
-- name    : DiscreteConvex_AlgorithmsC_IsMaximalMinimizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:24:23.111414+00:00
-- url     : https://prove2.me/theorems/04c37fb1-82d0-47da-acf0-8932860b095b
-- title:
--   IsMaximalMinimizer
-- statement:
--   $W$ is the maximal minimizer of $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.291, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.291, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOf

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `W` is the maximal minimizer of `ρ`. -/
def IsMaximalMinimizer (rho : Finset V → ℤ) (W : Finset V) : Prop :=
  IsMinimizerOf rho W ∧ ∀ W', IsMinimizerOf rho W' → W' ⊆ W

end DiscreteConvex.AlgorithmsC


