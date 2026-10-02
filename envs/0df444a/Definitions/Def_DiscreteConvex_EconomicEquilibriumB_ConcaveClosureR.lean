-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConcaveClosureR
-- name    : DiscreteConvex_EconomicEquilibriumB_ConcaveClosureR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:55:53.324229+00:00
-- url     : https://prove2.me/theorems/bea280ae-d2d6-4d72-abd9-38f47185f104
-- title:
--   ConcaveClosureR
-- statement:
--   The concave closure $\hat U$ of a utility-type function $U$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), redeclared, dualized.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), redeclared, dualized

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The concave closure `Û` of a utility-type function `U`. -/
noncomputable def ConcaveClosureR (U : (K → ℤ) → WithBot ℝ) (x : K → ℝ) : EReal :=
  sInf {v : EReal | ∃ (p : K → ℝ) (alpha : ℝ),
    (∀ y : K → ℤ, ToERealOfBot (U y) ≤ ((alpha + ∑ k, p k * (y k : ℝ) : ℝ) : EReal)) ∧
    v = ((alpha + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB


