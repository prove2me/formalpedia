-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_SBF
-- name    : DiscreteConvex_ConjugacyDualityC_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:00.107418+00:00
-- url     : https://prove2.me/theorems/161f9a7a-4b36-4607-8112-227e4e3f37cb
-- title:
--   SBF
-- statement:
--   Axiom (SBF[Z]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[Z]): `g(p)+g(q) ≥ g(p∨q)+g(p∧q)`. -/
def SBF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.ConjugacyDualityC


