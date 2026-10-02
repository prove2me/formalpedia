-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimalMinimizerWT
-- name    : DiscreteConvex_AlgorithmsC_IsMinimalMinimizerWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:25:12.708762+00:00
-- url     : https://prove2.me/theorems/ce166ee0-0495-4f7f-8d9e-d285c22978b7
-- title:
--   IsMinimalMinimizerWT
-- statement:
--   $W$ is the minimal minimizer of $\rho$: a minimizer contained in every other minimizer.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, tie-breaking rule (10.33).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.306, tie-breaking rule (10.33)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsC_IsMinimizerOfWT

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `W` is the *minimal* minimizer of `ρ`: a minimizer contained in every other minimizer. -/
def IsMinimalMinimizerWT (rho : Finset V → WithTop ℝ) (W : Finset V) : Prop :=
  IsMinimizerOfWT rho W ∧ ∀ W', IsMinimizerOfWT rho W' → W ⊆ W'

end DiscreteConvex.AlgorithmsC


