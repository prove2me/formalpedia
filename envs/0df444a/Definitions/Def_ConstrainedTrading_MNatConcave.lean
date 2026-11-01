-- Prove2me | Definitions.Def_ConstrainedTrading_MNatConcave
-- name    : ConstrainedTrading_MNatConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:58.359786+00:00
-- url     : https://prove2.me/theorems/28188902-bbac-4216-aea1-00d0a93a74f9
-- title:
--   M$^\sharp$-concave function with values in $\mathbb R\cup\{-\infty\}$
-- statement:
--   Let $f:\mathbb Z^E\to\mathbb R\cup\{-\infty\}$ with domain $\operatorname{dom} f=\{x : f(x)>-\infty\}$. The function $f$ is **M$^\sharp$-concave** if for all $x,y\in\operatorname{dom} f$ and every $u\in\operatorname{supp}^+(x-y)$ one of the following holds:
--
--   1. $f(x)+f(y)\le f(x-\chi_u)+f(y+\chi_u)$;
--   2. there is $v\in\operatorname{supp}^-(x-y)$ with
--   $$
--   f(x)+f(y)\le f(x-\chi_u+\chi_v)+f(y+\chi_u-\chi_v).
--   $$
--
--   This is the paper's Definition 2.7 applied to $-f$ ("$f$ is M$^\sharp$-concave if $-f$ is M$^\sharp$-convex", p.5), with values in $\mathbb R\cup\{-\infty\}$ as allowed by footnote 3 (p.3) so that trading constraints can be encoded by $-\infty$. M$^\sharp$-concave valuations are the gross-substitutes valuations of the trading-network literature.
--
--   **Formalization Note** $f$ is `(E → ℤ) → WithBot ℝ`, $\bot$ playing $-\infty$, and sums are taken in `WithBot ℝ`. Definition 2.7 quantifies over "$x,y\in B$" without naming $B$; it is read as the domain. There is no requirement that $\operatorname{dom} f$ be nonempty, as in the paper.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, Definition 2.7, p.4, and the definition of M♯-concave and dom f, p.5; footnote 3, p.3

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_CharVec
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppPos
import Definitions.Def_DiscreteConvex_MConvexSetsB_SuppNeg

open DiscreteConvex.MConvexSetsB

namespace ConstrainedTrading

/-- **M♯-concave function** (Kizilkale–Vohra, *Constrained Trading Networks*,
arXiv:2008.09757v1, Definition 2.7, p.4, and the sentence after it, p.5: `f` is M♯-concave if
`−f` is M♯-convex; values in `ℝ ∪ {−∞}` per footnote 3, p.3). For all `x, y` in the domain
`dom f = {x | f x ≠ −∞}` and every `u ∈ supp⁺(x − y)` one of the following holds:

* `f(x) + f(y) ≤ f(x − χ_u) + f(y + χ_u)`;
* there is `v ∈ supp⁻(x − y)` with `f(x) + f(y) ≤ f(x − χ_u + χ_v) + f(y + χ_u − χ_v)`.

**Formalization Note** `f : (E → ℤ) → WithBot ℝ`, with `⊥` the value `−∞`; sums are taken in
`WithBot ℝ` (`⊥ + a = ⊥`). This is Definition 2.7 applied to `−f`, written as the disjunction
form of the exchange (equivalently `f x + f y ≤ max(f(x−χ_u)+f(y+χ_u), max_v …)`). As in the
paper's Definition 2.7 there is **no** nonemptiness requirement on `dom f`; the constantly `⊥`
function is M♯-concave. -/
def MNatConcave {E : Type*} [DecidableEq E] (f : (E → ℤ) → WithBot ℝ) : Prop :=
  ∀ x y : E → ℤ, f x ≠ ⊥ → f y ≠ ⊥ → ∀ u ∈ SuppPos x y,
    f x + f y ≤ f (fun w => x w - CharVec u w) + f (fun w => y w + CharVec u w) ∨
    ∃ v ∈ SuppNeg x y,
      f x + f y ≤ f (fun w => x w - CharVec u w + CharVec v w) +
        f (fun w => y w + CharVec u w - CharVec v w)

end ConstrainedTrading


