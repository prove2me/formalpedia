-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsB_DiscreteConvexUnivariate
-- name    : DiscreteConvex_LConvexFunctionsB_DiscreteConvexUnivariate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:21:16.583986+00:00
-- url     : https://prove2.me/theorems/65156f62-f5b8-4ed2-b4f9-5529c43b7791
-- title:
--   DiscreteConvexUnivariate
-- statement:
--   A univariate function $\psi:\mathbb Z\to\mathbb R\cup\{+\infty\}$ is discrete convex (the book's $C[\mathbb Z\to\mathbb R]$).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, class $C[\\mathbb Z\\to\\mathbb R]$.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.183, class $C[\\mathbb Z\\to\\mathbb R]$

import Mathlib

namespace DiscreteConvex.LConvexFunctionsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A univariate function `ψ : Z → R∪{+∞}` is discrete convex (the book's `C[Z→R]`). -/
def DiscreteConvexUnivariate (psi : ℤ → WithTop ℝ) : Prop :=
  (∃ x, psi x ≠ ⊤) ∧ ∀ x : ℤ, psi x + psi (x + 2) ≥ psi (x + 1) + psi (x + 1)

end DiscreteConvex.LConvexFunctionsB


