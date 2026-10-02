-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
-- name    : DiscreteConvex_NetworkFlowsC_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:47:47.869975+00:00
-- url     : https://prove2.me/theorems/9c22fc9d-b22b-4470-b4c7-bb6d1f36e25f
-- title:
--   SBF
-- statement:
--   Axiom (SBF[Z]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Axiom (SBF[Z]). -/
def SBF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.NetworkFlowsC


