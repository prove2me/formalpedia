-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_HoleFree
-- name    : DiscreteConvex_IntegralConvexityB_HoleFree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:04:21.845866+00:00
-- url     : https://prove2.me/theorems/2197c209-1796-418a-9d60-01a6d4ce7f38
-- title:
--   Hole-free discrete set
-- statement:
--   $S=\bar S\cap\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.50)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_ConvexClosureSet
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.50): the hole-free property, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `S` is **hole free** (Eq. (3.50)): `S = S̄ ∩ Zⱽ`, i.e. every integer point of `S`'s convex
hull already belongs to `S`. -/
def HoleFree {V : Type*} (S : Set (V → ℤ)) : Prop :=
  ∀ x : V → ℤ, x ∈ S ↔ EmbedZR x ∈ ConvexClosureSet S

end DiscreteConvex.IntegralConvexityB


