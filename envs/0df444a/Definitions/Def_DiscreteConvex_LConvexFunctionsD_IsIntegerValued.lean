-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_IsIntegerValued
-- name    : DiscreteConvex_LConvexFunctionsD_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:06.996585+00:00
-- url     : https://prove2.me/theorems/a6b8a021-3db2-4278-ab13-6928d73f7d2e
-- title:
--   IsIntegerValued
-- statement:
--   $\rho:2^V\to\mathbb R\cup\{+\infty\}$ is integer valued.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `ρ : 2^V → R∪{+∞}` is integer valued. -/
def IsIntegerValued (rho : Finset V → WithTop ℝ) : Prop := ∀ X, ∃ k : ℤ, rho X = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexFunctionsD


