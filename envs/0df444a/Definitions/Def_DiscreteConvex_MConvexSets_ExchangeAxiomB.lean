-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomB
-- name    : DiscreteConvex_MConvexSets_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:21.667726+00:00
-- url     : https://prove2.me/theorems/0db45e1c-8648-43d7-9bd0-7f5ccb39e02e
-- title:
--   M-convex set exchange axiom (B-EXC[Z])
-- statement:
--   Axiom **(B-EXC[Z])**: for $x,y \in B$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ such that both $x - \chi_u + \chi_v$ and $y + \chi_u - \chi_v$ lie in $B$. A nonempty set $B \subseteq \mathbb Z^V$ satisfying this is an **M-convex set**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_CharVec
import Definitions.Def_DiscreteConvex_MConvexSets_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSets_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.101, axiom (B-EXC[Z]): the M-convex set
exchange axiom, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- Axiom **(B-EXC[Z])**: for `x, y ∈ B` and `u ∈ supp⁺(x-y)`, there is `v ∈ supp⁻(x-y)` such
that both `x - χ_u + χ_v` and `y + χ_u - χ_v` lie in `B`. A nonempty set `B ⊆ Zⱽ` satisfying
this is an **M-convex set**. -/
def ExchangeAxiomB {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSets


