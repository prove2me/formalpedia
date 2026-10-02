-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctions_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:53:21.982707+00:00
-- url     : https://prove2.me/theorems/11f4287e-97e3-4cb2-82c1-ded61e3781d5
-- title:
--   M-convex function exchange axiom (M-EXC[Z], Eq. 6.1)
-- statement:
--   Axiom **(M-EXC[Z])**: for $x, y \in \operatorname{dom} f$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $f(x) + f(y) \ge f(x-\chi_u+\chi_v) + f(y+\chi_u-\chi_v)$. A function $f : \mathbb Z^V \to \mathbb R \cup \{+\infty\}$ with $\operatorname{dom} f \ne \emptyset$ satisfying this is an **M-convex function**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, Eq. (6.1), axiom (M-EXC[Z]): the
M-convex function exchange axiom, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- Axiom **(M-EXC[Z])** (Eq. (6.1)): for `x, y ∈ dom f` and `u ∈ supp⁺(x-y)`, there is
`v ∈ supp⁻(x-y)` with `f(x) + f(y) ≥ f(x - χ_u + χ_v) + f(y + χ_u - χ_v)`. A function
`f : Zⱽ → R ∪ {+∞}` with `dom f ≠ ∅` satisfying this is an **M-convex function**. -/
def MExchangeAxiom {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctions


