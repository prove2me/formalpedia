-- Prove2me | Definitions.Def_NonmonotoneLS_RLinear_Run
-- name    : NonmonotoneLS_RLinear_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:21:34.860702+00:00
-- url     : https://prove2.me/theorems/73fa9eba-32d4-467a-8fbc-f2ecb8f63663
-- title:
--   Runs of the nonmonotone line search algorithm and the direction assumption
-- statement:
--   Fix parameters as in the NLSA initialization, a function $f : \mathbb{R}^n \to \mathbb{R}$ and a line-search rule, either the nonmonotone Wolfe conditions or the nonmonotone Armijo conditions, used for the whole run. A **run** of the Nonmonotone Line Search Algorithm consists of iterates $x_k$, directions $d_k$, steps $\alpha_k$ and weights $\eta_k$ ($k = 0, 1, 2, \dots$) such that for every $k$:
--
--   1. $x_{k+1} = x_k + \alpha_k d_k$;
--   2. $\eta_k \in [\eta_{\min}, \eta_{\max}]$;
--   3. $\alpha_k$ is a step accepted by the chosen rule at $(x_k, d_k)$ with reference value $C_k$ of (1.6).
--
--   With $g_k = \nabla f(x_k)$, the directions satisfy the **direction assumption with constants** $c_1, c_2$ if
--
--   $$g_k^{\mathsf T} d_k \le -c_1 \|g_k\|^2 \quad (2.4), \qquad \|d_k\| \le c_2 \|g_k\| \quad (2.5)$$
--
--   for **every** $k \ge 0$.
--
--   **Formalization Note.** The directions $d_k$ are arbitrary; theorems about runs hold for every direction sequence meeting their hypotheses. The run is infinite: the stopping test is not modelled, as in the paper's analysis. The rule is fixed per run, because the paper's theorems are stated per rule. The paper's direction assumption asks for (2.4)–(2.5) only "for all sufficiently large $k$"; the predicate here is the every-$k$ version that the proof of Theorem 3.1 uses (see the goal theorem's note), and statements quantify the constants $c_1, c_2 > 0$ themselves.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1044 (NLSA) and pp. 1046–1047, Direction Assumption, Eqs. (2.4)–(2.5)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps

open scoped InnerProductSpace

namespace NonmonotoneLS.RLinear

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

/-- The direction assumption (2.4)–(2.5) with constants `c₁, c₂`, required at **every** `k`:
`∇f(x_k) d_k ≤ -c₁ ‖∇f(x_k)‖²` and `‖d_k‖ ≤ c₂ ‖∇f(x_k)‖`. -/
def DirectionBounds (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (c₁ c₂ : ℝ) : Prop :=
  ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
    ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖

end NonmonotoneLS.RLinear


