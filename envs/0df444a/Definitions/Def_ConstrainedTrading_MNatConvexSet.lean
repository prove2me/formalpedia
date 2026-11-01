-- Prove2me | Definitions.Def_ConstrainedTrading_MNatConvexSet
-- name    : ConstrainedTrading_MNatConvexSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:54.281538+00:00
-- url     : https://prove2.me/theorems/0b15be0e-f0a1-4407-bb56-a7186792d17f
-- title:
--   M$^\sharp$-convex set
-- statement:
--   A set $B\subseteq\mathbb Z^E$ is **M$^\sharp$-convex** if for all $x,y\in B$ and every $u\in\operatorname{supp}^+(x-y)=\{e : x_e>y_e\}$ one of the following holds:
--
--   1. $x-\chi_u\in B$ and $y+\chi_u\in B$;
--   2. there is $v\in\operatorname{supp}^-(x-y)=\{e : x_e<y_e\}$ such that $x-\chi_u+\chi_v\in B$ and $y+\chi_u-\chi_v\in B$.
--
--   Here $\chi_u$ is the unit vector of coordinate $u$. Dropping the first alternative gives the M-convex sets of Definition 2.3, so every M-convex set is M$^\sharp$-convex. The integer points of an integral polymatroid, and the sets $B_f(x)$ of the mission, are M$^\sharp$-convex but in general not M-convex.
--
--   **Formalization Note** $\mathbb Z^E$ is `E → ℤ`; $\chi_u$, $\operatorname{supp}^\pm(x-y)$ are the published helpers `CharVec`, `SuppPos`, `SuppNeg` of `DiscreteConvex.MConvexSetsB`, shared with the published M-convex exchange axiom. As in the paper there is no nonemptiness clause.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.6, p.4

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppNeg

open DiscreteConvex.MConvexSetsB

namespace ConstrainedTrading

/-- **M♯-convex set** (Kizilkale–Vohra, *Constrained Trading Networks*, arXiv:2008.09757v1,
Definition 2.6, p.4). A set `B ⊆ ℤ^E` is M♯-convex if for all `x, y ∈ B` and every
`u ∈ supp⁺(x − y)` one of the following holds:

* `x − χ_u ∈ B` and `y + χ_u ∈ B`;
* there is `v ∈ supp⁻(x − y)` with `x − χ_u + χ_v ∈ B` and `y + χ_u − χ_v ∈ B`.

**Formalization Note** `ℤ^E` is `E → ℤ`. `χ_u`, `supp⁺(x − y)` and `supp⁻(x − y)` are the
published helpers `CharVec`, `SuppPos x y`, `SuppNeg x y` of `DiscreteConvex.MConvexSetsB`, the
same vocabulary as the published M-convex exchange axiom `ExchangeAxiomB` (Definition 2.3).
As on the page, there is no nonemptiness clause, so `∅` is M♯-convex. -/
def MNatConvexSet {E : Type*} [DecidableEq E] (B : Set (E → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ SuppPos x y,
    ((fun w => x w - CharVec u w) ∈ B ∧ (fun w => y w + CharVec u w) ∈ B) ∨
    ∃ v ∈ SuppNeg x y,
      (fun w => x w - CharVec u w + CharVec v w) ∈ B ∧
      (fun w => y w + CharVec u w - CharVec v w) ∈ B

end ConstrainedTrading


