-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
-- name    : DiscreteConvex_EconomicEquilibriumB_IsConcaveExtensible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:04:37.99184+00:00
-- url     : https://prove2.me/theorems/4132887e-24b4-40d7-9dae-9a508d8ede30
-- title:
--   IsConcaveExtensible
-- statement:
--   $U$ is concave-extensible: it agrees with its own concave closure on its domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, redeclared property.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, redeclared property

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ToERealOfBot
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ConcaveClosureR

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `U` is concave-extensible: it agrees with its own concave closure on its domain. -/
def IsConcaveExtensible (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ x : K → ℤ, x ∈ UDom U → ConcaveClosureR U (fun v => (x v : ℝ)) = ToERealOfBot (U x)

end DiscreteConvex.EconomicEquilibriumB


