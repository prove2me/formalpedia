-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_ExchangeAxiomBWeak
-- name    : DiscreteConvex_MConvexSets_ExchangeAxiomBWeak
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:18:19.377312+00:00
-- url     : https://prove2.me/theorems/ed4b5ccc-4ae6-45ff-9302-90baa36f39f5
-- title:
--   Weak exchange axiom (B-EXCw[Z])
-- statement:
--   Axiom **(B-EXCw[Z])**: for distinct $x,y \in B$, there exist $u \in \operatorname{supp}^+(x-y)$ and $v \in \operatorname{supp}^-(x-y)$ such that both $x-\chi_u+\chi_v$ and $y+\chi_u-\chi_v$ lie in $B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, axiom (B-EXCw[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, axiom (B-EXCw[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_CharVec
import Definitions.Def_DiscreteConvex_MConvexSets_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSets_SuppNeg

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, axiom (B-EXCw[Z]): the "weak" variant of
the M-convex set exchange axiom, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- Axiom **(B-EXCw[Z])**: for distinct `x, y ∈ B`, there exist `u ∈ supp⁺(x-y)` and
`v ∈ supp⁻(x-y)` such that both `x - χ_u + χ_v` and `y + χ_u - χ_v` lie in `B`. -/
def ExchangeAxiomBWeak {V : Type*} [DecidableEq V] (B : Set (V → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∃ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
    (fun w => y w + CharVec u w - CharVec v w) ∈ B

end DiscreteConvex.MConvexSets


