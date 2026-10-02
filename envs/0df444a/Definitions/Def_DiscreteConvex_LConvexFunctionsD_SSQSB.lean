-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_SSQSB
-- name    : DiscreteConvex_LConvexFunctionsD_SSQSB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:59:46.945789+00:00
-- url     : https://prove2.me/theorems/3aab8ae8-733d-4586-ad8f-425913ce74e1
-- title:
--   SSQSB
-- statement:
--   Axiom (SSQSB): $g$ is semistrictly quasi submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSB).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.199, axiom (SSQSB)

import Mathlib

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Axiom (SSQSB): `g` is semistrictly quasi submodular. -/
def SSQSB (g : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ p q : V → ℤ, (g (p ⊔ q) ≥ g q → g (p ⊓ q) ≤ g p) ∧ (g (p ⊓ q) ≥ g p → g (p ⊔ q) ≤ g q)

end DiscreteConvex.LConvexFunctionsD


