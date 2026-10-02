-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_IsIntegerValuedArcZ
-- name    : DiscreteConvex_NetworkFlowsB_IsIntegerValuedArcZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:09.244536+00:00
-- url     : https://prove2.me/theorems/d75a7ef5-52d5-41c9-91c9-a31362504f8b
-- title:
--   IsIntegerValuedArcZ
-- statement:
--   A univariate function $g:\mathbb Z\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, univariate.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, redeclared, univariate

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate function `g : Z → R ∪ {+∞}` is integer valued. -/
def IsIntegerValuedArcZ (g : ℤ → WithTop ℝ) : Prop :=
  ∀ t : ℤ, g t = ⊤ ∨ ∃ n : ℤ, g t = ((n : ℝ) : WithTop ℝ)

end DiscreteConvex.NetworkFlowsB


