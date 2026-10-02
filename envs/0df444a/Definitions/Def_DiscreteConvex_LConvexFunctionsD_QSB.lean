-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSB
-- name    : DiscreteConvex_LConvexFunctionsD_QSB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:51.280416+00:00
-- url     : https://prove2.me/theorems/663f5161-0181-4e5b-beb4-2e476155636f
-- title:
--   QSB
-- statement:
--   Axiom (QSB): $g$ is quasi submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSB).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (QSB)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (QSB): `g` is quasi submodular. -/
def QSB (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, g (p ⊓ q) ≤ g p ∨ g (p ⊔ q) ≤ g q

end DiscreteConvex.LConvexFunctionsD


