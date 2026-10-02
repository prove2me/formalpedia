-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBPlus
-- name    : DiscreteConvex_MConvexSets_ExchangeAxiomBPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:31.052546+00:00
-- url     : https://prove2.me/theorems/c6851068-07e5-4514-8f20-434a02c05807
-- title:
--   One-sided plus exchange axiom (B-EXC+[Z])
-- statement:
--   Axiom **(B-EXC+[Z])**: for $x,y \in B$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $y+\chi_u-\chi_v \in B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, axiom (B-EXC+[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, axiom (B-EXC+[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_CharVec
import Definitions.Def_DiscreteConvex_MConvexSets_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSets_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.102, axiom (B-EXC+[Z]): the "one-sided plus"
variant of the M-convex set exchange axiom, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- Axiom **(B-EXC+[Z])**: for `x, y ∈ B` and `u ∈ supp⁺(x-y)`, there is `v ∈ supp⁻(x-y)` such
that `y + χ_u - χ_v ∈ B` (only the `y`-side of (B-EXC[Z]) is required). -/
def ExchangeAxiomBPlus {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSets


