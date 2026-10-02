-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS
-- name    : DiscreteConvex_MConvexFunctionsC_MNatGS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:48.250428+00:00
-- url     : https://prove2.me/theorems/e26bea80-5462-45b6-94fa-c17302434952
-- title:
--   MNatGS
-- statement:
--   Axiom (M$^\natural$-GS[Z]), the M$^\natural$-version of the gross substitutes property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Eq. (6.64)-(6.65).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Eq. (6.64)-(6.65)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M♮-GS[Z]), Eq. (6.64)-(6.65)-adjacent. -/
def MNatGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℝ, ∀ p0 q0 : ℝ, (∀ v, p v ≤ q v) → p0 ≤ q0 →
    ∀ x ∈ ArgMinOn (LinearWeight f (fun v => p v - p0)),
    (ArgMinOn (LinearWeight f (fun v => q v - q0))).Nonempty →
    ∃ y ∈ ArgMinOn (LinearWeight f (fun v => q v - q0)),
      (∀ v, p v = q v → y v ≥ x v) ∧ (p0 = q0 → ∑ v, y v ≤ ∑ v, x v)

end DiscreteConvex.MConvexFunctionsC


