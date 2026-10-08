-- Prove2me | Definitions.Def_GVRPricing_Structure_IsHJBSolution
-- name    : GVRPricing_Structure_IsHJBSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:25:27.6361+00:00
-- url     : https://prove2.me/theorems/5a5ec83b-c5e5-41a7-854c-526ecc566b21
-- title:
--   Eq. (8) — the Hamilton–Jacobi system $\partial_t J(n,t) = \sup_{\lambda\in\Lambda}[r(\lambda) - \lambda(J(n,t)-J(n-1,t))]$ and optimal intensities
-- statement:
--   Fix a regular demand function with allowable rates $\Lambda$ and revenue rate $r$. A function $J(n,t)$ of the stock $n \in \{0,1,2,\dots\}$ and the **time remaining** $t \ge 0$ is a **solution of the Hamilton–Jacobi system (8)** if
--
--   1. $J(0,t) = 0$ for all $t \ge 0$ and $J(n,0) = 0$ for all $n$ (boundary conditions);
--   2. each $t \mapsto J(n,t)$ is continuous on $[0,\infty)$;
--   3. for every $n \ge 1$ and $t > 0$, writing $\Delta = J(n,t) - J(n-1,t)$ for the marginal value of an item, the values $\{r(\lambda) - \lambda\Delta : \lambda\in\Lambda\}$ are bounded above and
--   $$\frac{\partial J(n,t)}{\partial t} = \sup_{\lambda\in\Lambda}\big[r(\lambda) - \lambda\big(J(n,t) - J(n-1,t)\big)\big].$$
--
--   For such a $J$, an **optimal intensity** at $(n,t)$, $n\ge1$, is an allowable rate $\ell\in\Lambda$ attaining this supremum, i.e. maximizing $\lambda\mapsto r(\lambda) - \lambda(J(n,t)-J(n-1,t))$ over $\Lambda$; the corresponding **optimal price** is $p(\ell)$.
--
--   The paper derives (8) heuristically from the principle of optimality and cites Brémaud's verification theorem for the fact that a solution of (8) is the optimal expected revenue $J^*(n,t)$ and that the maximizing intensities form an optimal control. The structural results of the paper (Proposition 1, Theorem 1, the closed form (9)–(10) and Proposition 3) are proved directly on the solution of (8); this mission states them for that solution.
--
--   **Formalization Note** `J : ℕ → ℝ → ℝ`; the second argument is time-to-go, as in (8), not elapsed time. The derivative is the two-sided derivative `HasDerivAt` at every $t>0$, and continuity on $[0,\infty)$ makes the boundary value at $t=0$ attained. The bounded-above clause guarantees that the real supremum `sSup` is the genuine supremum and never a default value (for an unbounded $\Lambda$ and a negative marginal value the set would be unbounded). The objective $\lambda \mapsto r(\lambda)-\lambda\Delta$ is named `hamObjective`. This mission does not define $J^*$ as a supremum over pricing policies; that object and its identification with the solution of (8) (Brémaud's theorem, cited not proved by the paper) are outside its scope.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1004 (PDF 6), §2.2.1, eq. (8) and its boundary conditions

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model

namespace GVRPricing.Structure

/-- The objective inside the supremum of the HJB equation (8) (Gallego–van Ryzin 1994, p. 1004):
`λ ↦ r(λ) − λ Δ`, where `Δ = J(n, t) − J(n − 1, t)` is the marginal value of an item. -/
def hamObjective (M : Model) (Δ : ℝ) (x : ℝ) : ℝ := M.r x - x * Δ

/-- `J : ℕ → ℝ → ℝ` solves the Hamilton–Jacobi system (8) of Gallego–van Ryzin 1994 (§2.2.1,
p. 1004), with `J n t` the revenue-to-go with `n` items in stock and **time remaining** `t`:

* boundary conditions `J(0, t) = 0` for `t ≥ 0` and `J(n, 0) = 0` for all `n`;
* each `J(n, ·)` is continuous on `[0, ∞)` (so the boundary value at `t = 0` is attained);
* for `n ≥ 1` and `t > 0`, with `Δ = J(n, t) − J(n − 1, t)`, the set
  `{r(λ) − λ Δ : λ ∈ Λ}` is bounded above and
  `∂J(n, t)/∂t = sup_{λ ∈ Λ} [r(λ) − λ Δ]`.

The supremum ranges over the allowable rates `Λ`. -/
def IsHJBSolution (M : Model) (J : ℕ → ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → J 0 t = 0) ∧
  (∀ n : ℕ, J n 0 = 0) ∧
  (∀ n : ℕ, ContinuousOn (J n) (Set.Ici 0)) ∧
  ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 < t →
    BddAbove (hamObjective M (J n t - J (n - 1) t) '' M.Λ) ∧
    HasDerivAt (J n) (sSup (hamObjective M (J n t - J (n - 1) t) '' M.Λ)) t

/-- `ℓ` is an **optimal intensity** at stock `n` and time-to-go `t` for `J`: an allowable rate
that attains the supremum in (8), i.e. maximizes `λ ↦ r(λ) − λ (J(n, t) − J(n − 1, t))` over `Λ`.
The corresponding **optimal price** is `p(ℓ)`. Meaningful for `n ≥ 1`. -/
def IsOptimalIntensity (M : Model) (J : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) (ℓ : ℝ) : Prop :=
  ℓ ∈ M.Λ ∧ IsMaxOn (hamObjective M (J n t - J (n - 1) t)) M.Λ ℓ

end GVRPricing.Structure


