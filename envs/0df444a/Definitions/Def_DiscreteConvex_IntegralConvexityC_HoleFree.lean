-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_HoleFree
-- name    : DiscreteConvex_IntegralConvexityC_HoleFree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:11:20.797455+00:00
-- url     : https://prove2.me/theorems/5a8869ac-abcb-4d32-8a5c-cd9325288d7c
-- title:
--   Hole-free discrete set
-- statement:
--   $S=\bar S\cap\mathbb Z^n$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityC_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.50): the hole-free property, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S` is **hole free** (Eq. (3.50)): `S = S̄ ∩ Zⁿ`. -/
def HoleFree {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∀ x : Fin n → ℤ, x ∈ S ↔ EmbedZR x ∈ ConvexClosureSet S

end DiscreteConvex.IntegralConvexityC


