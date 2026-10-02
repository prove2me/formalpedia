-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
-- name    : DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:53:32.083752+00:00
-- url     : https://prove2.me/theorems/cf548e0b-6f3e-4cad-87ad-cadd3d192d77
-- title:
--   M-natural-convex function exchange axiom (M-nat-EXC[Z], Eq. 6.5)
-- statement:
--   Axiom **(M$^\natural$-EXC[Z])**: for $x,y \in \operatorname{dom} f$ and $u \in \operatorname{supp}^+(x-y)$, $f(x)+f(y) \ge \min\big(f(x-\chi_u)+f(y+\chi_u),\ \min_{v \in \operatorname{supp}^-(x-y)}[f(x-\chi_u+\chi_v)+f(y+\chi_u-\chi_v)]\big)$.
--
--   **Formalization Note.** The inner minimum is `Finset.inf`, which evaluates to $+\infty$ when $\operatorname{supp}^-(x-y) = \emptyset$, matching the book's stated convention for an empty minimum.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.5).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, Eq. (6.5)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.134, Eq. (6.5), axiom (M♮-EXC[Z]): the
M♮-convex function exchange axiom, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- Axiom **(M♮-EXC[Z])** (Eq. (6.5)): for `x, y ∈ dom f` and `u ∈ supp⁺(x-y)`,
`f(x) + f(y) ≥ min(f(x - χ_u) + f(y + χ_u), min_{v ∈ supp⁻(x-y)}[f(x - χ_u + χ_v) + f(y + χ_u
- χ_v)])`. The inner minimum over `supp⁻(x-y)` is `Finset.inf`, which is `⊤` (vacuously true)
when `supp⁻(x-y) = ∅`, matching the book's stated convention for an empty minimum. -/
def MNatExchangeAxiom {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    Prop :=
  ∀ x ∈ DomZ f, ∀ y ∈ DomZ f, ∀ u ∈ SuppPos x y,
    f x + f y ≥ min (f (fun w => x w - CharVec u w) + f (fun w => y w + CharVec u w))
      ((SuppNeg x y).inf (fun v =>
        f (fun w => x w - CharVec u w + CharVec v w) +
          f (fun w => y w + CharVec u w - CharVec v w)))

end DiscreteConvex.MConvexFunctions


