-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_ZVec
-- name    : DiscreteConvex_AlgorithmsB_ZVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:58:36.444179+00:00
-- url     : https://prove2.me/theorems/53d6fde5-75ff-44b1-9dc7-9c6011c77fe6
-- title:
--   ZVec
-- statement:
--   $z=x+\partial\phi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, preceding Eq. (10.21).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.296, preceding Eq. (10.21)

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_FlowBoundary

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `z = x + ∂ϕ`. -/
def ZVec (x : V → ℝ) (phi : V → V → ℝ) (v : V) : ℝ := x v + FlowBoundary phi v

end DiscreteConvex.AlgorithmsB


