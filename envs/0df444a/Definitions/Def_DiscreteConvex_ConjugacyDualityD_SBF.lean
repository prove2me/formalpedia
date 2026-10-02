-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_SBF
-- name    : DiscreteConvex_ConjugacyDualityD_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:56.526782+00:00
-- url     : https://prove2.me/theorems/398a57f4-b187-4505-8f50-f9a176870854
-- title:
--   SBF
-- statement:
--   Axiom (SBF[Z]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]), redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[Z]): `g(p)+g(q) ≥ g(p∨q)+g(p∧q)`. -/
def SBF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.ConjugacyDualityD


