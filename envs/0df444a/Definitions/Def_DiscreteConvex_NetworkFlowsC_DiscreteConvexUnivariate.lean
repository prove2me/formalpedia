-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
-- name    : DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:48:24.897367+00:00
-- url     : https://prove2.me/theorems/7f1df11e-3f8b-432e-a855-ae4219b6a8a7
-- title:
--   DiscreteConvexUnivariate
-- statement:
--   A univariate function $\psi:\mathbb Z\to\mathbb R\cup\{+\infty\}$ is discrete convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- A univariate function `ψ : Z → R∪{+∞}` is discrete convex. -/
def DiscreteConvexUnivariate (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.NetworkFlowsC


