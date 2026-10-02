-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMinTop
-- name    : DiscreteConvex_EconomicEquilibrium_ArgMinTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:35.190918+00:00
-- url     : https://prove2.me/theorems/57f1ae44-8c13-4dc6-86f5-972911ce6754
-- title:
--   Minimizer set of a WithTop-valued function
-- statement:
--   The minimizer set $\arg\min f = \{x \in \mathbb Z^K : f(x) \le f(y)\ \forall y \in \mathbb Z^K\}$ of $f : \mathbb Z^K \to \mathbb R \cup \{+\infty\}$. Used to form the supply set $S_l(p) = \arg\min C_l[-p]$, equivalent to $\arg\max_y(\langle p,y\rangle - C_l(y))$ (Eq. (11.1)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1), restated via the `Cl[−p]`
notation used from p.336 on (`yl ∈ arg min Cl[−p]`): the minimizer set of a `WithTop ℝ`-valued
function, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The minimizer set `arg min f = {x ∈ Zᴷ : f(x) ≤ f(y) ∀y ∈ Zᴷ}` of `f : Zᴷ → R ∪ {+∞}`. -/
def ArgMinTop {K : Type*} (f : (K → ℤ) → WithTop ℝ) : Set (K → ℤ) :=
  {x | ∀ y, f x ≤ f y}

end DiscreteConvex.EconomicEquilibrium


