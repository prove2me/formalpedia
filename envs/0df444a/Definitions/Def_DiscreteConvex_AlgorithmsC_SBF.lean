-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_SBF
-- name    : DiscreteConvex_AlgorithmsC_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:18:18.356267+00:00
-- url     : https://prove2.me/theorems/51973dc1-e2f2-4eb5-b4a0-143217b723e3
-- title:
--   SBF
-- statement:
--   Axiom (SBF[Z]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[Z]). -/
def SBF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.AlgorithmsC


