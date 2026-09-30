-- Prove2me | Definitions.Def_DRCVRP_FirstOrder_ConvexProgram
-- name    : DRCVRP_FirstOrder_ConvexProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:51:35.02264+00:00
-- url     : https://prove2.me/theorems/5c3efd38-86c7-4047-8767-f21ef6ace154
-- title:
--   The convex program (13) for the worst-case value-at-risk
-- statement:
--   Let $V_C=\{1,\dots,n\}$ be the customers, $\underline{\boldsymbol q}\le\boldsymbol\mu\le\overline{\boldsymbol q}$ vectors in $\mathbb R^n$ (support bounds and mean), $S_1,\dots,S_p\subseteq V_C$ customer subsets with bounds $\boldsymbol\nu\in\mathbb R^p$, $\epsilon\in(0,1)$ a risk level and $S\subseteq V_C$ a customer subset. For $A\subseteq V_C$ write $\mathbf 1_A\in\{0,1\}^n$ for its indicator vector. Define the componentwise minimum
--
--   $$
--   \hat{\boldsymbol q}=\min\Bigl\{\overline{\boldsymbol q}-\boldsymbol\mu,\ \tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q})\Bigr\},
--   $$
--
--   and, for $\boldsymbol\gamma\in\mathbb R^p$, the objective of problem (13),
--
--   $$
--   f_S(\boldsymbol\gamma)=\mathbf 1_S^\top\boldsymbol\mu+\hat{\boldsymbol q}^\top\Bigl[\mathbf 1_S-2\sum_{i=1}^p\gamma_i\mathbf 1_{S_i}\Bigr]_+ +\frac1\epsilon\,\boldsymbol\nu^\top\boldsymbol\gamma,
--   $$
--
--   where $[\cdot]_+$ is the componentwise positive part and the inner product runs over all customers $j\in V_C$. Problem (13) minimizes $f_S$ over the nonnegative orthant $\boldsymbol\gamma\in\mathbb R^p_+$.
--
--   This convex, piecewise-linear objective is the right-hand side of Theorem 5, and $\hat{\boldsymbol q}$ also appears in the closed forms (14) and (15) of Corollaries 2 and 3.
--
--   **Formalization Note** Customers are `Fin n` and subsets are indexed by `Fin p`; `qhat` is the vector $\hat{\boldsymbol q}$, and `convexProgramObjective` is $f_S$ written with explicit indicator values $0$/$1$.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, p. 726, Theorem 5, problem (13); q̂ as defined below Eqs. (14) and (15)

import Mathlib

namespace DRCVRP.FirstOrder

/-!
The optimization problem (13) of Ghosal and Wiesemann, *The Distributionally Robust
Chance-Constrained Vehicle Routing Problem*, Oper. Res. 68(3) (2020), §5.1, p. 726, Theorem 5.
Customers are `Fin n` (0-based), the customer subsets `S_1, …, S_p` are `Sfam : Fin p → Finset
(Fin n)`, and `γ : Fin p → ℝ` is the decision vector of (13).
-/

/-- The vector `q̂ = min {(q̄ − μ), ((1 − ε)/ε)(μ − q̲)}`, minimum taken componentwise
(§5.1, p. 726, Theorem 5, Corollaries 2 and 3). -/
noncomputable def qhat {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (j : Fin n) : ℝ :=
  min (qhi j - μ j) ((1 - ε) / ε * (μ j - qlo j))

/-- The objective function of problem (13) (§5.1, p. 726):
`1_Sᵀ μ + min {(q̄ − μ), ((1 − ε)/ε)(μ − q̲)}ᵀ · [1_S − 2 ∑_{l=1}^p γ_l 1_{S_l}]₊ + (1/ε) νᵀ γ`.
The positive part `[·]₊` is taken componentwise, and the inner product runs over all customers
`j ∈ V_C`. -/
noncomputable def convexProgramObjective {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin p → Finset (Fin n)) (ν : Fin p → ℝ) (ε : ℝ) (S : Finset (Fin n))
    (γ : Fin p → ℝ) : ℝ :=
  ∑ j ∈ S, μ j +
    ∑ j, qhat qlo qhi μ ε j *
      max 0 ((if j ∈ S then 1 else 0) - 2 * ∑ l, γ l * (if j ∈ Sfam l then 1 else 0)) +
    (1 / ε) * ∑ l, ν l * γ l

end DRCVRP.FirstOrder


