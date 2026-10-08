-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Extras
-- name    : GlobalInexactNewton_Backtracking_Extras
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:33:48.777011+00:00
-- url     : https://prove2.me/theorems/c1fd8a72-59f3-43ac-9446-bf9da5689d5c
-- title:
--   Actual and predicted reductions (2.4), and runs of Algorithms TL and ENB
-- statement:
--   Let $E$ be a real normed space (in the paper, $\mathbb R^n$ with an arbitrary norm) and $F:E\to E$, with derivative $F'(x)$ at $x$.
--
--   1. **Actual and predicted reductions (2.4).** For a step $s$ from a point $x$,
--   $$\mathrm{ared}(s)=\|F(x)\|-\|F(x+s)\|,\qquad\mathrm{pred}(s)=\|F(x)\|-\|F(x)+F'(x)s\|.$$
--   The predicted reduction is the decrease of the norm of the local linear model; the actual reduction is the decrease of $\|F\|$ itself.
--   2. **Algorithm TL** (trust level method, p. 407). Given $x_0$, $\bar\eta_0\in[0,1)$, $0<t\le u<1$ and $0<\theta_{\min}<\theta_{\max}<1$, iteration $k$ determines a curve $\sigma_k$ with
--   $$\|F(x_k)+F'(x_k)\sigma_k(\eta)\|\le\eta\|F(x_k)\|\qquad(\bar\eta_k\le\eta\le1)\tag{5.1}$$
--   and sets $\eta_k=\bar\eta_k$; while $\|F(x_k+\sigma_k(\eta_k))\|>[1-t(1-\eta_k)]\|F(x_k)\|$ it chooses $\theta\in[\theta_{\min},\theta_{\max}]$ and updates $\eta_k\leftarrow1-\theta(1-\eta_k)$. It then sets $x_{k+1}=x_k+\sigma_k(\eta_k)$, and chooses $\bar\eta_{k+1}\in[0,\eta_k]$ if $\|F(x_{k+1})\|\le[1-u(1-\eta_k)]\|F(x_k)\|$, and $\bar\eta_{k+1}\in[0,1-\theta_{\min}(1-\eta_k)]$ otherwise.
--   3. **Algorithm ENB** (exact Newton method with backtracking, p. 411). Given $x_0$, $t\in(0,1)$ and $0<\theta_{\min}<\theta_{\max}<1$, iteration $k$ solves $F'(x_k)s_k=-F(x_k)$; while $\mathrm{ared}_k(s_k)<t\cdot\mathrm{pred}_k(s_k)$ it chooses $\theta\in[\theta_{\min},\theta_{\max}]$ and updates $s_k\leftarrow\theta s_k$; then $x_{k+1}=x_k+s_k$.
--
--   TL adapts the initial inexact Newton level to the agreement observed between $F$ and its linear model at earlier iterations; ENB is Algorithm INB with $\eta_{\max}=0$, rephrased in terms of actual and predicted reductions. The reductions (2.4) are also the acceptance test of the trust region method (Algorithm TR, §4, p. 402).
--
--   **Formalization Note** The inexact Newton condition, the sufficient decrease condition (2.2) and the loop bookkeeping `trialLevel`/`trialStep` are imported from the companion definition of Algorithms GIN, MR and INB. As there, a run is an infinite sequence ("the algorithm does not break down", p. 396), and the while-loop of iteration $k$ is recorded by its number of passes $m_k$ and its factors $\theta_{k,0},\dots,\theta_{k,m_k-1}$, with every earlier trial failing the loop's test and the last one passing it. In ENB the solution of the Newton equation is the data `snewton k`, constrained by `fderiv ℝ F (x k) (snewton k) = -F (x k)`; $F'$ is `fderiv`, so the theorems that use these runs assume $F$ continuously differentiable.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 397 (2.4), p. 407 (Algorithm TL), p. 411 (Algorithm ENB)

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method

namespace GlobalInexactNewton.Backtracking

/-!
Eisenstat and Walker, *Globally Convergent Inexact Newton Methods*, SIAM J. Optim. 4(2) (1994),
p. 397 (2.4), p. 407 (Algorithm TL), p. 411 (Algorithm ENB): actual and predicted reductions, and
runs of Algorithms TL and ENB.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- (2.4): actual reduction `ared(s) = ‖F(x)‖ - ‖F(x + s)‖`. -/
def ared (F : E → E) (x s : E) : ℝ :=
  ‖F x‖ - ‖F (x + s)‖

/-- (2.4): predicted reduction `pred(s) = ‖F(x)‖ - ‖F(x) + F'(x) s‖`. -/
noncomputable def pred (F : E → E) (x s : E) : ℝ :=
  ‖F x‖ - ‖F x + fderiv ℝ F x s‖

/-- Algorithm TL (trust level method, p. 407) without breakdown. `η̄_0 = ηbar 0 ∈ [0,1)` and
`0 < t ≤ u < 1`. Iteration `k` takes a curve `σ k` with (5.1) on `[η̄_k, 1]`; its while-loop runs
`m k` times with factors `θ k j ∈ [θ_min, θ_max]`, every trial level `j < m k` fails (2.2) and the
level `η_k = trialLevel (ηbar k) (θ k) (m k)` passes it; `x_{k+1} = x_k + σ_k(η_k)`. Then
`η̄_{k+1} ∈ [0, η_k]` if `‖F(x_{k+1})‖ ≤ [1 - u(1 - η_k)] ‖F(x_k)‖`, and
`η̄_{k+1} ∈ [0, 1 - θ_min(1 - η_k)]` otherwise. -/
structure IsTLRun (F : E → E) (t u θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  tu_bounds : 0 < t ∧ t ≤ u ∧ u < 1
  θ_bounds : 0 < θmin ∧ θmin < θmax ∧ θmax < 1
  ηbar_zero_mem : ηbar 0 ∈ Set.Ico (0 : ℝ) 1
  curve : ∀ k, ∀ η ∈ Set.Icc (ηbar k) 1, InexactNewtonCond F (x k) (σ k η) η
  θ_mem : ∀ k, ∀ j < m k, θ k j ∈ Set.Icc θmin θmax
  rejected : ∀ k, ∀ j < m k,
    ¬ SuffDecrease F t (x k) (σ k (trialLevel (ηbar k) (θ k) j)) (trialLevel (ηbar k) (θ k) j)
  accepted : ∀ k,
    SuffDecrease F t (x k) (σ k (trialLevel (ηbar k) (θ k) (m k))) (trialLevel (ηbar k) (θ k) (m k))
  step : ∀ k, x (k + 1) = x k + σ k (trialLevel (ηbar k) (θ k) (m k))
  update_trusted : ∀ k,
    ‖F (x (k + 1))‖ ≤ (1 - u * (1 - trialLevel (ηbar k) (θ k) (m k))) * ‖F (x k)‖ →
      ηbar (k + 1) ∈ Set.Icc 0 (trialLevel (ηbar k) (θ k) (m k))
  update_untrusted : ∀ k,
    ¬ ‖F (x (k + 1))‖ ≤ (1 - u * (1 - trialLevel (ηbar k) (θ k) (m k))) * ‖F (x k)‖ →
      ηbar (k + 1) ∈ Set.Icc 0 (1 - θmin * (1 - trialLevel (ηbar k) (θ k) (m k)))

/-- Algorithm ENB (exact Newton method with backtracking, p. 411) without breakdown. Iteration `k`
solves `F'(x_k) s = -F(x_k)` (the solution is `snewton k`); its while-loop runs `m k` times with
factors `θ k j ∈ [θ_min, θ_max]`, every trial step `trialStep (snewton k) (θ k) j` with `j < m k`
has `ared < t · pred` and the final one `s_k` (index `m k`) has `ared ≥ t · pred`; then
`x_{k+1} = x_k + s_k`. -/
structure IsENBRun (F : E → E) (t θmin θmax : ℝ) (x : ℕ → E) (snewton : ℕ → E)
    (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  t_mem : t ∈ Set.Ioo (0 : ℝ) 1
  θ_bounds : 0 < θmin ∧ θmin < θmax ∧ θmax < 1
  newton : ∀ k, fderiv ℝ F (x k) (snewton k) = - F (x k)
  θ_mem : ∀ k, ∀ j < m k, θ k j ∈ Set.Icc θmin θmax
  rejected : ∀ k, ∀ j < m k,
    ared F (x k) (trialStep (snewton k) (θ k) j) < t * pred F (x k) (trialStep (snewton k) (θ k) j)
  accepted : ∀ k,
    t * pred F (x k) (trialStep (snewton k) (θ k) (m k)) ≤ ared F (x k) (trialStep (snewton k) (θ k) (m k))
  step : ∀ k, x (k + 1) = x k + trialStep (snewton k) (θ k) (m k)

end GlobalInexactNewton.Backtracking


