-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConvexClosureR
-- name    : DiscreteConvex_EconomicEquilibriumB_ConvexClosureR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:56:01.344724+00:00
-- url     : https://prove2.me/theorems/67b49dd4-8947-4841-9fc8-af5de66fe363
-- title:
--   ConvexClosureR
-- statement:
--   The convex closure $\hat C$ of a cost-type function $C$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eq. (3.56), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToEReal

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The convex closure `Ĉ` of a cost-type function `C`. -/
noncomputable def ConvexClosureR (C : (K → ℤ) → WithTop ℝ) (x : K → ℝ) : EReal :=
  sSup {v : EReal | ∃ (p : K → ℝ) (alpha : ℝ),
    (∀ y : K → ℤ, ((alpha + ∑ k, p k * (y k : ℝ) : ℝ) : EReal) ≤ ToEReal (C y)) ∧
    v = ((alpha + ∑ k, p k * x k : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB


