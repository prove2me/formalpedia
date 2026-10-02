-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContSupplySet
-- name    : DiscreteConvex_EconomicEquilibriumB_ContSupplySet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:04:46.047206+00:00
-- url     : https://prove2.me/theorems/2e6a5a26-7a92-46f2-b2c7-f0fef8271716
-- title:
--   ContSupplySet
-- statement:
--   The continuous supply set $\hat S_l(p)=\arg\max(\langle p,y\rangle-\hat C_l(y))$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.32), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.32), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConvexClosureR

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The continuous supply set `Ŝl(p) = arg max (⟨p,y⟩ − Ĉl(y))`. -/
def ContSupplySet (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {y | ∀ z : K → ℝ,
    ((∑ k, p k * z k : ℝ) : EReal) + (-ConvexClosureR C z) ≤
      ((∑ k, p k * y k : ℝ) : EReal) + (-ConvexClosureR C y)}

end DiscreteConvex.EconomicEquilibriumB


