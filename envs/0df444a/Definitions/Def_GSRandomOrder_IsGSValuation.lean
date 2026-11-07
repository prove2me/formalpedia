-- Prove2me | Definitions.Def_GSRandomOrder_IsGSValuation
-- name    : GSRandomOrder_IsGSValuation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:35.041447+00:00
-- url     : https://prove2.me/theorems/1f50ac7f-b638-4d2a-933b-842d3e109e57
-- title:
--   Gross substitutes (GS) valuation: the exchange axiom (3)
-- statement:
--   Let $N=\{1,\dots,n\}$ be a finite set of items. A **valuation** is a function $v:2^N\to\mathbb R\cup\{-\infty\}$ with $v(\emptyset)=0$; its **domain** is $\operatorname{dom}v=\{S: v(S)>-\infty\}$. Write $S+g=S\cup\{g\}$ and $S-g=S\setminus\{g\}$.
--
--   A valuation satisfies the **exchange axiom** if for all $X,Y\in\operatorname{dom}v$ and every $x\in X\setminus Y$,
--   $$
--   v(X)+v(Y)\le\max\Bigl\{\,v(X-x)+v(Y+x),\ \max_{y\in Y\setminus X}\bigl[v(X-x+y)+v(Y+x-y)\bigr]\Bigr\},
--   $$
--   where a maximum over the empty set is $-\infty$. A **GS valuation** is a valuation with this property; by the theorem of Fujishige–Yang and Shioura–Tamura cited in the paper (Theorem 2.3), this is equivalent to Kelso–Crawford gross substitutes defined through prices.
--
--   This is the class of valuations for which the paper's secretary algorithm selects each item of the optimum with probability $1/e$; it contains weighted matroid rank functions, assignment valuations and concave functions of the cardinality, minus any modular price vector.
--
--   **Formalization Note** Items are `Fin n`. Values lie in `WithBot ℝ` with $\bot=-\infty$, so $\bot+a=\bot$ and a set outside the domain makes its alternative $-\infty$. The inner maximum is `Finset.sup`, which is $\bot$ on an empty index set. No monotonicity, nonnegativity or finiteness is assumed.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §2, p.5 (valuations), Definition 2.2 and eq. (3), p.5; p.6 (definition of GS valuation)

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder

/-- **GS valuation** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in Random Order*,
STOC 2027 submission, manuscript sha256 69787f50…, §2, p.5, Definition 2.2 and eq. (3); p.6).

The ground set is `N = Fin n`. A *valuation* is a function `v : 2^N → ℝ ∪ {−∞}` with `v(∅) = 0`,
and `dom v = {S : v(S) > −∞}`. A valuation satisfies the *exchange axiom* if for all
`X, Y ∈ dom v` and every `x ∈ X \ Y`,
`v(X) + v(Y) ≤ max { v(X − x) + v(Y + x), max_{y ∈ Y \ X} [v(X − x + y) + v(Y + x − y)] }`,
where a maximum over the empty set is `−∞`. A *GS valuation* is a valuation with the exchange
axiom (p.6: the price definition 2.1 and the exchange axiom are equivalent by the cited
Theorem 2.3, and every proof of the paper uses the exchange axiom).

**Formalization Note.** Values live in `WithBot ℝ`, with `⊥ = −∞`; `X ∈ dom v` is `v X ≠ ⊥`.
`⊥ + a = ⊥` in `WithBot ℝ`, so an alternative containing a set outside `dom v` has value `−∞`. The
inner maximum is `Finset.sup`, whose value on the empty index set is `⊥ = −∞`, the paper's
convention. `X − x` is `X.erase x`, `Y + x` is `insert x Y`. No monotonicity, nonnegativity or
finiteness is assumed: valuations are signed and may take the value `−∞`. -/
def IsGSValuation {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) : Prop :=
  v ∅ = 0 ∧
    ∀ X Y : Finset (Fin n), v X ≠ ⊥ → v Y ≠ ⊥ → ∀ x ∈ X \ Y,
      v X + v Y ≤ max (v (X.erase x) + v (insert x Y))
        ((Y \ X).sup fun y => v (insert y (X.erase x)) + v ((insert x Y).erase y))

end GSRandomOrder


