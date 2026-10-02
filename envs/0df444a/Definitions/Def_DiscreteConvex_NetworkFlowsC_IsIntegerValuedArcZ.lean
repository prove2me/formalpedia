-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedArcZ
-- name    : DiscreteConvex_NetworkFlowsC_IsIntegerValuedArcZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:36.020745+00:00
-- url     : https://prove2.me/theorems/3aae1245-43b6-4732-9279-4c399da9e5e4
-- title:
--   IsIntegerValuedArcZ
-- statement:
--   A univariate function $g:\mathbb Z\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, univariate.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, univariate

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def IsIntegerValuedArcZ (g : ℤ → WithTop ℝ) : Prop :=
  ∀ t : ℤ, g t = ⊤ ∨ ∃ n : ℤ, g t = ((n : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsC


