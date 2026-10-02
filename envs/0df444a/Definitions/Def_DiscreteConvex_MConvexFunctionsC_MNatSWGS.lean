-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatSWGS
-- name    : DiscreteConvex_MConvexFunctionsC_MNatSWGS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:49.495978+00:00
-- url     : https://prove2.me/theorems/28329cf4-dfd1-4d9f-95da-1d09c70423bb
-- title:
--   MNatSWGS
-- statement:
--   Axiom (M$^\natural$-SWGS[Z]), the **stepwise gross substitutes property**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.155

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LinearWeight
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ArgMinOn

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (M♮-SWGS[Z]). -/
def MNatSWGS (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p : V → ℝ, ∀ x ∈ ArgMinOn (LinearWeight f p), ∀ u : V,
    (∀ alpha : ℝ, 0 ≤ alpha →
        x ∈ ArgMinOn (LinearWeight f (fun v => p v + (if v = u then alpha else 0)))) ∨
    (∃ alpha : ℝ, 0 ≤ alpha ∧
      ∃ y ∈ ArgMinOn (LinearWeight f (fun v => p v + (if v = u then alpha else 0))),
        y u = x u - 1 ∧ ∀ v, v ≠ u → y v ≥ x v)

end DiscreteConvex.MConvexFunctionsC


