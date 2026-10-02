-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_SBF
-- name    : DiscreteConvex_ConjugacyDualityB_SBF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:01.439376+00:00
-- url     : https://prove2.me/theorems/37c02135-ff80-4269-b180-42b9ac93e5af
-- title:
--   SBF
-- statement:
--   Axiom (SBF[Z]): $g(p)+g(q)\ge g(p\vee q)+g(p\wedge q)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.177, axiom (SBF[Z])

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SBF[Z]): `g(p)+g(q) ≥ g(p∨q)+g(p∧q)`. -/
def SBF (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.ConjugacyDualityB


