-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_IsMaximalMinimizer
-- name    : DiscreteConvex_AlgorithmsB_IsMaximalMinimizer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:02.740574+00:00
-- url     : https://prove2.me/theorems/91dc7a2e-17ee-4dd6-af0c-101f7074b030
-- title:
--   IsMaximalMinimizer
-- statement:
--   $W$ is the maximal minimizer of $\rho$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.291, Note 10.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.291, Note 10.11

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsMinimizerOf

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `W` is the maximal minimizer of `ρ`. -/
def IsMaximalMinimizer (rho : Finset V → ℤ) (W : Finset V) : Prop :=
  IsMinimizerOf rho W ∧ ∀ W', IsMinimizerOf rho W' → W' ⊆ W

end DiscreteConvex.AlgorithmsB


