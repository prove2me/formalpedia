-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_DiscreteConvexUnivariate
-- name    : DiscreteConvex_ConjugacyDualityD_DiscreteConvexUnivariate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:12.897335+00:00
-- url     : https://prove2.me/theorems/d8555b9f-b9df-4fc8-94cc-7c02c073a945
-- title:
--   DiscreteConvexUnivariate
-- statement:
--   A univariate function $\psi:\mathbb Z\to\mathbb R\cup\{+\infty\}$ is discrete convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, adjacent to Theorem 8.49.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.234, adjacent to Theorem 8.49

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A univariate function `ψ : Z → R∪{+∞}` is discrete convex. -/
def DiscreteConvexUnivariate (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.ConjugacyDualityD


