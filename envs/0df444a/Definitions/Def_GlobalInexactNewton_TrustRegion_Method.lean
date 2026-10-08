-- Prove2me | Definitions.Def_GlobalInexactNewton_TrustRegion_Method
-- name    : GlobalInexactNewton_TrustRegion_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:36.785979+00:00
-- url     : https://prove2.me/theorems/83316833-5a12-4bf0-ac84-72a48f819110
-- title:
--   Actual and predicted reduction (2.4), stationary points of ‖F‖, model minimizers (4.5), and runs of Algorithm TR
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$ (the paper's $\mathbf R^n$ with an arbitrary norm), let $F:E\to E$, and write $F'(x)$ for the Fréchet derivative of $F$ at $x$. All objects below are those of Eisenstat and Walker (1994).
--
--   1. **Actual and predicted reduction** (2.4). For a point $x$ and a step $s$,
--   $$\operatorname{ared}(s) = \|F(x)\| - \|F(x+s)\|,\qquad \operatorname{pred}(s) = \|F(x)\| - \|F(x) + F'(x)\,s\|.$$
--   The predicted reduction is the decrease of the norm of the local linear model $s\mapsto F(x)+F'(x)s$.
--   2. **Relative predicted reduction** (p. 402): $\operatorname{relpred}(s) = \operatorname{pred}(s)/\|F(x)\|$ if $F(x)\neq 0$, and $\operatorname{relpred}(s)=1$ otherwise.
--   3. **Stationary point of $\|F\|$** (p. 396): $x$ is a stationary point of $\|F\|$ if $\|F(x)\|\le\|F(x)+F'(x)s\|$ for every $s\in E$, i.e. no step decreases the norm of the local linear model.
--   4. **Model minimizer** (4.5): for $\delta\in\mathbf R$, a step $s$ satisfies (4.5) at $x$ if
--   $$s\in\arg\min_{\|\bar s\|\le\delta}\|F(x)+F'(x)\,\bar s\|,$$
--   that is, $\|s\|\le\delta$ and $\|F(x)+F'(x)s\|\le\|F(x)+F'(x)\bar s\|$ for every $\bar s$ with $\|\bar s\|\le\delta$.
--   5. **Algorithm TR** (trust region method, p. 402). Given $x_0$, $\bar\delta_0>0$, $0<t\le u<1$ and $0<\theta_{\min}<\theta_{\max}<1$, iteration $k$ sets $\delta_k=\bar\delta_k$ and chooses $s_k$ by (4.5) with $\delta=\delta_k$; while $\operatorname{ared}_k(s_k)<t\cdot\operatorname{pred}_k(s_k)$ it chooses $\theta\in[\theta_{\min},\theta_{\max}]$, replaces $\delta_k$ by $\theta\delta_k$ and chooses a new $s_k$ by (4.5). It then sets $x_{k+1}=x_k+s_k$, and chooses $\bar\delta_{k+1}\ge\delta_k$ if $\operatorname{ared}_k(s_k)\ge u\cdot\operatorname{pred}_k(s_k)$, and $\bar\delta_{k+1}\ge\theta_{\min}\delta_k$ otherwise.
--
--   A **run** of Algorithm TR records, for every $k$, the number $m_k$ of passes through the while-loop, the factors $\theta_{k,0},\dots,\theta_{k,m_k-1}\in[\theta_{\min},\theta_{\max}]$, the trial radii $\rho_{k,0}=\bar\delta_k$, $\rho_{k,j+1}=\theta_{k,j}\rho_{k,j}$, and trial steps $s_{k,0},\dots,s_{k,m_k}$, each satisfying (4.5) with $\delta=\rho_{k,j}$. Every trial $j<m_k$ is rejected ($\operatorname{ared}<t\cdot\operatorname{pred}$), the trial $m_k$ is accepted ($\operatorname{ared}\ge t\cdot\operatorname{pred}$), the accepted step is $s_k=s_{k,m_k}$, the final radius is $\delta_k=\rho_{k,m_k}$, $x_{k+1}=x_k+s_k$, and $\bar\delta_{k+1}$ obeys the update rule above.
--
--   These are the objects of the paper's Application 1 (§4): the global convergence analysis of trust region methods for $F(x)=0$ through the inexact Newton framework.
--
--   **Formalization Note.** $E$ is a finite-dimensional real normed space, which is exactly "$\mathbf R^n$ with an arbitrary norm". $F'$ is `fderiv ℝ F`. The minimizer in (4.5) need not be unique for a general norm, so (4.5) is a predicate on $s$, and a run may pick any minimizer, as the paper's "CHOOSE" allows. "Algorithm TR does not break down" (p. 396: it generates an infinite sequence of iterates) is the existence of a run: each while-loop ends after the finite number $m_k$ of passes. The new radius $\bar\delta_{k+1}$ has only the lower bound printed in the algorithm. Positivity of later radii follows from $\bar\delta_0>0$ and is not an extra field.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), pp. 396, 397, 402, 404: stationary point (p. 396), (2.4), relpred (p. 402), Algorithm TR (p. 402), (4.5)

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Extras

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- p. 402: `relpred(s) = GlobalInexactNewton.Backtracking.pred(s) / ‖F x‖` if `F x ≠ 0`, and `1` otherwise. -/
noncomputable def relpred (F : E → E) (x s : E) : ℝ :=
  if F x ≠ 0 then GlobalInexactNewton.Backtracking.pred F x s / ‖F x‖ else 1

/-- p. 396: `x` is a stationary point of `‖F‖` if `‖F x‖ ≤ ‖F x + F'(x) s‖` for every `s`. -/
def IsStationaryPtNorm (F : E → E) (x : E) : Prop :=
  ∀ s : E, ‖F x‖ ≤ ‖F x + fderiv ℝ F x s‖

/-- (4.5), p. 404: `s ∈ arg min_{‖s̄‖ ≤ δ} ‖F x + F'(x) s̄‖`. A predicate, since the minimizer
need not be unique for an arbitrary norm. -/
def IsLinModelMin (F : E → E) (x : E) (δ : ℝ) (s : E) : Prop :=
  ‖s‖ ≤ δ ∧ ∀ s' : E, ‖s'‖ ≤ δ → ‖F x + fderiv ℝ F x s‖ ≤ ‖F x + fderiv ℝ F x s'‖

/-- The radii visited by the while-loop of Algorithm TR in one iteration:
`ρ⁽⁰⁾ = δ̄` and `ρ⁽ʲ⁺¹⁾ = θ_j ρ⁽ʲ⁾`. -/
def trialRadius (δbar : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => δbar
  | j + 1 => θ j * trialRadius δbar θ j

/-- Algorithm TR (trust region method), p. 402, as a predicate on an infinite run.

Iteration `k` starts from the radius `δbar k` (= δ̄_k) and runs the while-loop `m k` times: trial
`j ≤ m k` uses the radius `trialRadius (δbar k) (θ k) j` and a step `s k j` minimizing the norm of
the local linear model over that ball. Every trial `j < m k` fails the acceptance test
`ared ≥ t · GlobalInexactNewton.Backtracking.pred` (so the loop shrinks the radius by a factor `θ k j ∈ [θmin, θmax]`), and trial
`m k` passes it. The accepted step is `s_k = s k (m k)`, the final radius is
`δ_k = trialRadius (δbar k) (θ k) (m k)`, `x (k+1) = x k + s_k`, and `δbar (k+1)` obeys the
radius-update rule. "Algorithm TR does not break down" (p. 396) is the existence of such a run. -/
structure IsTRRun (F : E → E) (t u θmin θmax : ℝ) (x : ℕ → E) (δbar : ℕ → ℝ)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (s : ℕ → ℕ → E) : Prop where
  /-- δ̄₀ > 0 is given. -/
  δbar_zero_pos : 0 < δbar 0
  /-- 0 < t ≤ u < 1. -/
  tu : 0 < t ∧ t ≤ u ∧ u < 1
  /-- 0 < θmin < θmax < 1. -/
  θ_bounds : 0 < θmin ∧ θmin < θmax ∧ θmax < 1
  /-- Every trial step minimizes the linear model over its trust region. -/
  argmin : ∀ k, ∀ j ≤ m k, IsLinModelMin F (x k) (trialRadius (δbar k) (θ k) j) (s k j)
  /-- Every shrink factor used by the loop lies in [θmin, θmax]. -/
  θ_mem : ∀ k, ∀ j < m k, θ k j ∈ Set.Icc θmin θmax
  /-- Every trial before the last one is rejected: GlobalInexactNewton.Backtracking.ared < t · GlobalInexactNewton.Backtracking.pred. -/
  rejected : ∀ k, ∀ j < m k, GlobalInexactNewton.Backtracking.ared F (x k) (s k j) < t * GlobalInexactNewton.Backtracking.pred F (x k) (s k j)
  /-- The last trial is accepted: GlobalInexactNewton.Backtracking.ared ≥ t · GlobalInexactNewton.Backtracking.pred. -/
  accepted : ∀ k, t * GlobalInexactNewton.Backtracking.pred F (x k) (s k (m k)) ≤ GlobalInexactNewton.Backtracking.ared F (x k) (s k (m k))
  /-- x_{k+1} = x_k + s_k. -/
  step : ∀ k, x (k + 1) = x k + s k (m k)
  /-- If GlobalInexactNewton.Backtracking.ared ≥ u · GlobalInexactNewton.Backtracking.pred, then δ̄_{k+1} ≥ δ_k. -/
  radius_up : ∀ k, u * GlobalInexactNewton.Backtracking.pred F (x k) (s k (m k)) ≤ GlobalInexactNewton.Backtracking.ared F (x k) (s k (m k)) →
    trialRadius (δbar k) (θ k) (m k) ≤ δbar (k + 1)
  /-- Otherwise δ̄_{k+1} ≥ θmin · δ_k. -/
  radius_down : ∀ k, GlobalInexactNewton.Backtracking.ared F (x k) (s k (m k)) < u * GlobalInexactNewton.Backtracking.pred F (x k) (s k (m k)) →
    θmin * trialRadius (δbar k) (θ k) (m k) ≤ δbar (k + 1)

end GlobalInexactNewton.TrustRegion


