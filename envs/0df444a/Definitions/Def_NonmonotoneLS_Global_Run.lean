-- Prove2me | Definitions.Def_NonmonotoneLS_Global_Run
-- name    : NonmonotoneLS_Global_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:17:54.673797+00:00
-- url     : https://prove2.me/theorems/f90a3e4f-73a1-4f28-bedc-5e4eec379d75
-- title:
--   Runs of the nonmonotone line search algorithm and the direction assumption (2.4)–(2.5)
-- statement:
--   Fix parameters as in the NLSA initialization, a function $f : \mathbb{R}^n \to \mathbb{R}$ and a line-search rule, either **Wolfe** or **Armijo**, used at every iteration. A **run** of the Nonmonotone Line Search Algorithm consists of iterates $x_k$, directions $d_k$, steps $\alpha_k$ and weights $\eta_k$ ($k = 0, 1, 2, \dots$) such that for every $k$
--
--   1. $x_{k+1} = x_k + \alpha_k d_k$;
--   2. $\eta_k \in [\eta_{\min}, \eta_{\max}]$;
--   3. $\alpha_k$ satisfies the nonmonotone Wolfe conditions (resp. the nonmonotone Armijo conditions) at $x_k$ with direction $d_k$ and reference value $C_k$ from (1.6).
--
--   The **direction assumption** holds if there are constants $c_1, c_2 > 0$ such that, writing $g_k = \nabla f(x_k)$,
--
--   $$g_k^{\mathsf T} d_k \le -c_1 \|g_k\|^2 \quad (2.4), \qquad \|d_k\| \le c_2 \|g_k\| \quad (2.5)$$
--
--   for all sufficiently large $k$.
--
--   **Formalization Note.** The run is infinite: the convergence test "if $\|\nabla f(x_k)\|$ is sufficiently small, stop" is not modelled, as in the paper's analysis (a stationary iterate can be continued with $d_k = 0$). The directions $d_k$ are arbitrary, constrained only by the hypotheses of each theorem. The rule is fixed for the whole run, matching the case split "if the Wolfe conditions are used … if the Armijo conditions are used" of Theorem 2.2.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1044 (NLSA) and pp. 1046–1047 (Direction Assumption, Eqs. (2.4)–(2.5))

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps

open scoped InnerProductSpace
open Filter

namespace NonmonotoneLS.Global

/-- Which line search the run uses: the nonmonotone Wolfe conditions or the nonmonotone
Armijo conditions. The rule is fixed for the whole run. -/
inductive Rule
  | wolfe
  | armijo

variable {n : ℕ}

/-- A step accepted by the rule `r`. -/
def IsStep (r : Rule) (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : EuclideanSpace ℝ (Fin n)) (C α : ℝ) : Prop :=
  match r with
  | Rule.wolfe => Shared.IsWolfeStep p f x d C α
  | Rule.armijo => Shared.IsArmijoStep p f x d C α

/-- An (infinite) run of the Nonmonotone Line Search Algorithm (p. 1044) with parameters `p`
and line-search rule `r`: iterates `x`, directions `d`, steps `α` and weights `η` with
`x_{k+1} = x_k + α_k d_k`, `η_k ∈ [η_min, η_max]`, and `α_k` accepted by the rule at
`(x_k, d_k)` with reference value `C_k` of (1.6). The convergence test is not modelled. -/
structure IsNLSARun (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ) : Prop where
  update : ∀ k, x (k + 1) = x k + α k • d k
  eta_mem : ∀ k, η k ∈ Set.Icc p.ηmin p.ηmax
  step : ∀ k, IsStep r p f (x k) (d k) (Shared.costC f x η k) (α k)

/-- The direction assumption (2.4)–(2.5): there are `c₁, c₂ > 0` with
`∇f(x_k) d_k ≤ -c₁ ‖∇f(x_k)‖²` and `‖d_k‖ ≤ c₂ ‖∇f(x_k)‖` for all sufficiently large `k`. -/
def DirectionAssumption (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ k in atTop,
    ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
      ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖

end NonmonotoneLS.Global


