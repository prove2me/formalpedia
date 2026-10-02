-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
-- name    : DiscreteConvex_EconomicEquilibriumB_MNaturalConcave
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:55:24.196981+00:00
-- url     : https://prove2.me/theorems/aa911e31-f795-4092-aefd-a8947d003daf
-- title:
--   MNaturalConcave
-- statement:
--   $U:\mathbb Z^K\to\mathbb R\cup\{-\infty\}$ is M$^\natural$-concave (axiom (−M$^\natural$-EXC[Z])).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Eq. (11.17), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, Eq. (11.17), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppPos
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppNeg

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `U : Zᴷ → R∪{−∞}` is M♮-concave (axiom (−M♮-EXC[Z]), Eq. (11.17)). -/
def MNaturalConcave (U : (K → ℤ) → WithBot ℝ) : Prop :=
  (UDom U).Nonempty ∧
  ∀ x ∈ UDom U, ∀ y ∈ UDom U, ∀ i ∈ SuppPos x y,
    U x + U y ≤ max
      (U (fun w => x w - (if w = i then (1:ℤ) else 0)) + U (fun w => y w + (if w = i then (1:ℤ) else 0)))
      ((SuppNeg x y).sup (fun j =>
        U (fun w => x w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
          U (fun w => y w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0))))

end DiscreteConvex.EconomicEquilibriumB


