-- Prove2me | Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
-- name    : ArrowDebreu_Shared_IsCompetitiveEquilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:36:41.254902+00:00
-- url     : https://prove2.me/theorems/58f77349-a254-4cec-9f7d-9b253c6ba04b
-- title:
--   Competitive equilibrium (Conditions 1–4, Definition 1.5.0)
-- statement:
--   Fix an economy with production sets $Y_j$, consumption sets $X_i$, utilities $u_i$, endowments $\zeta_i$ and shares $\alpha_{ij}$. For a price vector $p^*$, consumption vectors $x_1^*, \dots, x_m^*$ and production plans $y_1^*, \dots, y_n^*$ consider:
--
--   1. **Condition 1.** For each $j$, $y_j^*$ maximizes $p^*\cdot y_j$ over $Y_j$: $y_j^* \in Y_j$ and $p^*\cdot y_j \le p^*\cdot y_j^*$ for all $y_j \in Y_j$.
--   2. **Condition 2.** For each $i$, $x_i^*$ maximizes $u_i$ over the budget set
--   $$\Big\{x_i \in X_i : p^*\cdot x_i \leqq p^*\cdot\zeta_i + \sum_{j=1}^n \alpha_{ij}\, p^*\cdot y_j^*\Big\},$$
--   i.e. $x_i^*$ lies in this set and $u_i(x_i) \le u_i(x_i^*)$ for every $x_i$ in it.
--   3. **Condition 3.** $p^* \in P = \{p \in \mathbb R^l : p \geqq 0,\ \sum_h p_h = 1\}$.
--   4. **Condition 4.** With $z^* = \sum_i x_i^* - \sum_j y_j^* - \sum_i \zeta_i$: $z^* \leqq 0$ componentwise and $p^*\cdot z^* = 0$.
--
--   A tuple $(x_1^*, \dots, x_m^*, y_1^*, \dots, y_n^*, p^*)$ is a **competitive equilibrium** (Definition 1.5.0) if it satisfies Conditions 1–4.
--
--   Condition 1 is profit maximization, Condition 2 utility maximization under the budget constraint, Condition 3 the normalization of prices, and Condition 4 market clearing with free disposal of goods in excess supply at zero price.
--
--   It serves both missions of the series: `01-theorem-i` (the conclusion of Theorem I, p. 272, PDF p. 9) and `02-theorem-ii` (the conclusion of Theorem II, p. 281, PDF p. 18); both use Conditions 1–4 of pp. 268–271 (PDF pp. 5–8) and Definition 1.5.0 of p. 272 (PDF p. 9). It is reviewed once for both.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 268–272 (PDF pp. 5–9), Condition 1 (§1.2.3), Condition 2 (§1.3.3), Condition 3 (§1.4.0), Condition 4 (§1.4.1), Definition 1.5.0

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy

namespace ArrowDebreu.Shared

variable {l m n : ℕ}

/-- **Condition 1** (§1.2.3, p. 268, PDF p. 5): `y_j^*` maximizes `p^*·y_j` over the set `Y_j`,
for each `j` — i.e. `y_j^* ∈ Y_j` and `p^*·y_j ≤ p^*·y_j^*` for every `y_j ∈ Y_j`. -/
def Condition1 (E : Economy l m n) (p : Fin l → ℝ) (y : Fin n → Fin l → ℝ) : Prop :=
  ∀ j, y j ∈ E.Y j ∧ ∀ y' ∈ E.Y j, p ⬝ᵥ y' ≤ p ⬝ᵥ y j

/-- The budget set `{x_i | x_i ∈ X_i, p·x_i ≦ p·ζ_i + Σ_{j=1}^n α_{ij} p·y_j}` of consumer `i`
(Condition 2, p. 271, PDF p. 8). -/
def budgetSet (E : Economy l m n) (p : Fin l → ℝ) (y : Fin n → Fin l → ℝ) (i : Fin m) :
    Set (Fin l → ℝ) :=
  {x | x ∈ E.X i ∧ p ⬝ᵥ x ≤ income E p y i}

/-- **Condition 2** (§1.3.3, p. 271, PDF p. 8): for each `i`, `x_i^*` maximizes `u_i(x_i)` over the
set `{x_i | x_i ∈ X_i, p^*·x_i ≦ p^*·ζ_i + Σ_{j=1}^n α_{ij} p^*·y_j^*}` — i.e. `x_i^*` belongs to
that set and `u_i(x_i) ≤ u_i(x_i^*)` for every `x_i` in it. -/
def Condition2 (E : Economy l m n) (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) : Prop :=
  ∀ i, x i ∈ budgetSet E p y i ∧ ∀ x' ∈ budgetSet E p y i, E.u i x' ≤ E.u i (x i)

/-- **Condition 3** (§1.4.0, p. 271, PDF p. 8): `p^* ∈ P = {p | p ∈ R^l, p ≧ 0, Σ_h p_h = 1}`. -/
def Condition3 (p : Fin l → ℝ) : Prop :=
  p ∈ priceSimplex l

/-- **Condition 4** (§1.4.1, p. 271, PDF p. 8): `z^* ≦ 0` (componentwise) and `p^*·z^* = 0`, where
`z = Σ_i x_i − Σ_j y_j − Σ_i ζ_i`. -/
def Condition4 (E : Economy l m n) (p : Fin l → ℝ) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) : Prop :=
  excessDemand E x y ≤ 0 ∧ p ⬝ᵥ excessDemand E x y = 0

/-- **Definition 1.5.0** (p. 272, PDF p. 9): a set of vectors `(x_1^*, ⋯, x_m^*, y_1^*, ⋯, y_n^*, p^*)`
is a *competitive equilibrium* if it satisfies Conditions 1–4. -/
def IsCompetitiveEquilibrium (E : Economy l m n) (x : Fin m → Fin l → ℝ)
    (y : Fin n → Fin l → ℝ) (p : Fin l → ℝ) : Prop :=
  Condition1 E p y ∧ Condition2 E p x y ∧ Condition3 p ∧ Condition4 E p x y

end ArrowDebreu.Shared


