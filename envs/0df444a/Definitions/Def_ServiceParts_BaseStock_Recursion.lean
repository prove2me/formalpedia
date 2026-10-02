-- Prove2me | Definitions.Def_ServiceParts_BaseStock_Recursion
-- name    : ServiceParts_BaseStock_Recursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T21:23:09.032187+00:00
-- url     : https://prove2.me/theorems/a993dec8-fcaf-4a9b-a076-257ae7b6489d
-- title:
--   n-period value functions $f_n$, optimal orders, and the marginal function $F_n$
-- statement:
--   In the model of Section 2.1 with lead time one period, let $f_n(y)$ be the minimum expected discounted cost when $n$ periods remain and the inventory position is $y$. The value functions are defined by
--   $$
--   f_1(y) = L(y), \qquad f_n(y) = \min_{u \ge 0}\Big\{ c\,u + L(y) + \alpha\int_0^\infty f_{n-1}(y+u-x)\,g(x)\,dx \Big\} \quad (n \ge 2),
--   $$
--   where $u$ is the quantity ordered. For $n \ge 2$ an order $u$ is **optimal** at position $y$ if $u \ge 0$ and $u$ minimises the bracket over all $u' \ge 0$. The **order-up-to rule with level $s$** orders
--   $$
--   u(y) = \max\{0,\ s - y\},
--   $$
--   and it is called optimal for horizon $n$ when it gives an optimal order at every $y$. Finally, as in eq. (2.8),
--   $$
--   F_n(w) = c + \alpha\int_0^\infty f_n'(w-x)\,g(x)\,dx .
--   $$
--
--   These objects carry the induction in the proof of Theorem 2: $F_{n-1}$ is the derivative of the minimand with respect to the target position $w = y+u$.
--
--   **Formalization Note** The minimum in the recursion is written as the infimum over $u \ge 0$; the costs are nonnegative, so the infimum is over a nonempty set bounded below, and statements that assert an optimal order assert that it is attained. Optimality is always against all orders $u' \ge 0$, never only against order-up-to rules. `f 0` is the constant $0$ and is used by no statement. $F_n$ is written with Lean's `deriv`; statements that rely on $f_n'$ assert differentiability separately.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 18-19 and p. 21, Section 2.1, proof of Theorem 2 (the recursion for f_n, eq. (2.5), eq. (2.8), f_1(y) = L(y))

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model

open MeasureTheory Set

namespace ServiceParts.BaseStock

/-- The quantity minimised in the recursion of p. 18 when the continuation value is `V`:
`c·u + L(y) + α ∫₀^∞ V(y + u − x) g(x) dx`, for inventory position `y` and order `u`. -/
noncomputable def Model.stageCost (M : Model) (V : ℝ → ℝ) (y u : ℝ) : ℝ :=
  M.c * u + M.L y + M.α * ∫ x in Ioi (0 : ℝ), V (y + u - x) * M.g x

/-- The n-period value functions `f n` = the book's `fₙ` (p. 18 and p. 21), lead time τ = 1:
`f₁(y) = L(y)` and `fₙ(y) = min_{u ≥ 0} {c·u + L(y) + α ∫₀^∞ fₙ₋₁(y + u − x) g(x) dx}` for
`n ≥ 2`, the minimum written as the infimum over `u ≥ 0`. The value at index `0` is the
constant `0`; it is not used by any statement of the mission. -/
noncomputable def Model.f (M : Model) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => M.L
  | n + 2 => fun y => sInf (M.stageCost (M.f (n + 1)) y '' Ici 0)

/-- The objective of the `n`-period problem at inventory position `y` and order quantity `u`
(meaningful for `n ≥ 2`): `c·u + L(y) + α ∫₀^∞ fₙ₋₁(y + u − x) g(x) dx`. -/
noncomputable def Model.orderCost (M : Model) (n : ℕ) (y u : ℝ) : ℝ :=
  M.stageCost (M.f (n - 1)) y u

/-- `u` is an optimal order in the `n`-period problem at inventory position `y`: `u ≥ 0` and
it minimises the objective over **all** order quantities `u' ≥ 0`. -/
def Model.IsOptimalOrder (M : Model) (n : ℕ) (y u : ℝ) : Prop :=
  0 ≤ u ∧ ∀ u' : ℝ, 0 ≤ u' → M.orderCost n y u ≤ M.orderCost n y u'

/-- The order-up-to rule with level `s`, `u(y) = max{0, s − y}` (eq. (2.5)), is optimal in the
`n`-period problem at every inventory position `y`. -/
def Model.IsOrderUpToOptimal (M : Model) (n : ℕ) (s : ℝ) : Prop :=
  ∀ y : ℝ, M.IsOptimalOrder n y (max 0 (s - y))

/-- The function `Fₙ(w) = c + α ∫₀^∞ f′ₙ(w − x) g(x) dx` of eq. (2.8), p. 19. -/
noncomputable def Model.F (M : Model) (n : ℕ) (w : ℝ) : ℝ :=
  M.c + M.α * ∫ x in Ioi (0 : ℝ), deriv (M.f n) (w - x) * M.g x

end ServiceParts.BaseStock


