-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomBPlus
-- name    : DiscreteConvex_MConvexSetsB_ExchangeAxiomBPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:42.195067+00:00
-- url     : https://prove2.me/theorems/c7b94c5e-19d6-45a3-9ba6-5aa682bca275
-- title:
--   ExchangeAxiomBPlus
-- statement:
--   Axiom **(B-EXC+[Z])**: for $x,y \in B$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $y+\chi_u-\chi_v \in B$ (only the $y$-side of (B-EXC[Z]) is required).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, axiom (B-EXC+[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.102, axiom (B-EXC+[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.102, axiom (B-EXC+[Z]): the "one-sided
plus" variant of the M-convex set exchange axiom, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Axiom **(B-EXC+[Z])**: for `x, y ∈ B` and `u ∈ supp⁺(x-y)`, there is `v ∈ supp⁻(x-y)` such
that `y + χ_u - χ_v ∈ B` (only the `y`-side of (B-EXC[Z]) is required). -/
def ExchangeAxiomBPlus {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSetsB


