-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:08:12.861673+00:00
-- url     : https://prove2.me/theorems/5e902e45-af67-4f79-be8c-e16eaf428677
-- title:
--   MExchangeAxiom
-- statement:
--   Axiom **(M-EXC[Z])**, Eq. (6.1): for $x,y \in \operatorname{dom} f$ and $u \in \operatorname{supp}^+(x-y)$, there is $v \in \operatorname{supp}^-(x-y)$ with $f(x)+f(y) \ge f(x-\chi_u+\chi_v)+f(y+\chi_u-\chi_v)$. A function satisfying this is an **M-convex function**.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, Eq. (6.1)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.133, Eq. (6.1), in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Axiom **(M-EXC[Z])** (Eq. (6.1)): `f` is an **M-convex function**. -/
def MExchangeAxiom {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) : Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y, ∃ v ∈ SuppNeg x y,
    f x + f y ≥ f (fun w => x w - CharVec u w + CharVec v w) +
      f (fun w => y w + CharVec u w - CharVec v w)

end DiscreteConvex.MConvexFunctionsB


