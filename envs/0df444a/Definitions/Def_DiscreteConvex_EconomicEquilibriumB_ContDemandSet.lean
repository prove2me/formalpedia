-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContDemandSet
-- name    : DiscreteConvex_EconomicEquilibriumB_ContDemandSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:04:33.027302+00:00
-- url     : https://prove2.me/theorems/db4bd49e-f285-4c2b-a677-0eae0d81e232
-- title:
--   ContDemandSet
-- statement:
--   The continuous demand set $\hat D_h(p)=\arg\max(\hat U_h(x)-\langle p,x\rangle)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.31), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337, Eq. (11.31), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConcaveClosureR

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The continuous demand set `D̂h(p) = arg max (Ûh(x) − ⟨p,x⟩)`. -/
def ContDemandSet (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℝ) :=
  {x | ∀ z : K → ℝ,
    ConcaveClosureR U z + ((-(∑ k, p k * z k) : ℝ) : EReal) ≤
      ConcaveClosureR U x + ((-(∑ k, p k * x k) : ℝ) : EReal)}

end DiscreteConvex.EconomicEquilibriumB


