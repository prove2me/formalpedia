-- Prove2me | Definitions.Def_GlobalInexactNewton_Backtracking_Method
-- name    : GlobalInexactNewton_Backtracking_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:20:49.639823+00:00
-- url     : https://prove2.me/theorems/26f147ab-c2c6-4115-ba08-48e941c844a6
-- title:
--   Inexact Newton condition (2.1), sufficient decrease (2.2), and runs of Algorithms GIN, MR and INB
-- statement:
--   Let $E$ be a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$ (this is $\mathbb R^n$ with an arbitrary norm), and let $F:E\to E$ with Fréchet derivative $F'(x)$. Fix $t\in(0,1)$.
--
--   1. **Inexact Newton condition (2.1).** A step $s$ from $x$ is an inexact Newton step at level $\eta$ if
--   $$\|F(x)+F'(x)s\|\le\eta\,\|F(x)\|.$$
--   2. **Sufficient decrease (2.2).** The step $s$ gives sufficient decrease at level $\eta$ if
--   $$\|F(x+s)\|\le[1-t(1-\eta)]\,\|F(x)\|.$$
--   3. **Algorithm GIN** (global inexact Newton method). A run is a sequence $x_0,x_1,\dots$ with levels $\eta_k\in[0,1)$ such that each step $s_k=x_{k+1}-x_k$ satisfies (2.1) and (2.2) at level $\eta_k$.
--   4. **Trial levels and trial steps.** Given an initial level $\bar\eta$, an initial step $\bar s$ and factors $\theta_0,\theta_1,\dots$, the while-loops below visit the levels $\eta^{(0)}=\bar\eta$, $\eta^{(j+1)}=1-\theta_j(1-\eta^{(j)})$, and (in INB) the steps $s^{(0)}=\bar s$, $s^{(j+1)}=\theta_j s^{(j)}$.
--   5. **Algorithm MR** (minimum reduction method). Given $\eta_{\max}\in[0,1)$, $t\in(0,1)$ and $0<\theta_{\min}<\theta_{\max}<1$, iteration $k$ chooses $\bar\eta_k\in[0,\eta_{\max}]$ and a curve $\sigma_k$ satisfying
--   $$\|F(x_k)+F'(x_k)\sigma_k(\eta)\|\le\eta\,\|F(x_k)\|,\qquad\bar\eta_k\le\eta\le1, \tag{5.1}$$
--   starts at $\eta_k=\bar\eta_k$, and while $\|F(x_k+\sigma_k(\eta_k))\|>[1-t(1-\eta_k)]\|F(x_k)\|$ chooses $\theta\in[\theta_{\min},\theta_{\max}]$ and updates $\eta_k\leftarrow1-\theta(1-\eta_k)$; then $x_{k+1}=x_k+\sigma_k(\eta_k)$.
--   6. **Algorithm INB** (inexact Newton backtracking method). Same parameters. Iteration $k$ chooses $\bar\eta_k\in[0,\eta_{\max}]$ and $\bar s_k$ with $\|F(x_k)+F'(x_k)\bar s_k\|\le\bar\eta_k\|F(x_k)\|$, starts at $s_k=\bar s_k$, $\eta_k=\bar\eta_k$, and while $\|F(x_k+s_k)\|>[1-t(1-\eta_k)]\|F(x_k)\|$ chooses $\theta\in[\theta_{\min},\theta_{\max}]$ and updates $s_k\leftarrow\theta s_k$, $\eta_k\leftarrow1-\theta(1-\eta_k)$; then $x_{k+1}=x_k+s_k$.
--
--   These are the objects of every statement of the mission: GIN is the general framework, MR the paradigm, INB the practical backtracking method.
--
--   **Formalization Note** $F'(x)$ is `fderiv ℝ F x`. A run is a predicate on infinite sequences: the paper says an algorithm "does not break down" when it generates an infinite sequence of iterates (p. 396), so the run predicate is that hypothesis. The steps and levels the paper says to "find" or "choose" are data constrained only by the stated conditions. The while-loop of iteration $k$ is recorded by the number $m_k$ of times its body ran and the factors $\theta_{k,0},\dots,\theta_{k,m_k-1}\in[\theta_{\min},\theta_{\max}]$: each trial $j<m_k$ fails the loop test (so the loop continues) and trial $m_k$ passes it. The final values are $\eta_k=\eta^{(m_k)}$ and, in INB, $s_k=s^{(m_k)}$. The curve $\sigma_k$ is a function $\mathbb R\to E$ constrained only on $[\bar\eta_k,1]$.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 396 (Algorithm GIN, (2.1), (2.2)), p. 407 ((5.1), Algorithm MR), p. 410 (Algorithm INB)

import Mathlib

namespace GlobalInexactNewton.Backtracking

/-!
Eisenstat and Walker, *Globally Convergent Inexact Newton Methods*, SIAM J. Optim. 4(2) (1994),
pp. 396, 407, 410: the inexact Newton condition (2.1), the sufficient decrease condition (2.2), and
runs of Algorithms GIN (p. 396), MR (p. 407) and INB (p. 410).

Formalization Note: `Rⁿ` with an arbitrary norm is a real normed space `E` (the theorems add
`[FiniteDimensional ℝ E]`), and `F'(x)` is `fderiv ℝ F x`. A run is a predicate on infinite
sequences: "the algorithm does not break down" means that it generates an infinite sequence of
iterates (p. 396). The while-loop of iteration `k` runs its body `m k` times with factors
`θ k 0, …, θ k (m k - 1)`; every trial before the last fails the loop's test and the last one
passes it.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- (1.3)/(2.1): `s` is an inexact Newton step from `x` at level `η`,
`‖F(x) + F'(x) s‖ ≤ η ‖F(x)‖`. -/
def InexactNewtonCond (F : E → E) (x s : E) (η : ℝ) : Prop :=
  ‖F x + fderiv ℝ F x s‖ ≤ η * ‖F x‖

/-- (2.2): sufficient decrease of `‖F‖` along `s` with parameter `t` at level `η`,
`‖F(x + s)‖ ≤ [1 - t(1 - η)] ‖F(x)‖`. -/
def SuffDecrease (F : E → E) (t : ℝ) (x s : E) (η : ℝ) : Prop :=
  ‖F (x + s)‖ ≤ (1 - t * (1 - η)) * ‖F x‖

/-- Algorithm GIN (p. 396) without breakdown: `t ∈ (0,1)`, and for every `k` a level
`η k ∈ [0,1)` such that the step `s_k = x (k+1) - x k` satisfies (2.1) and (2.2). -/
structure IsGINRun (F : E → E) (t : ℝ) (x : ℕ → E) (η : ℕ → ℝ) : Prop where
  t_mem : t ∈ Set.Ioo (0 : ℝ) 1
  eta_mem : ∀ k, η k ∈ Set.Ico (0 : ℝ) 1
  inexact : ∀ k, InexactNewtonCond F (x k) (x (k + 1) - x k) (η k)
  decrease : ∀ k, SuffDecrease F t (x k) (x (k + 1) - x k) (η k)

/-- The levels visited by the while-loops of Algorithms MR, TL and INB:
`η⁽⁰⁾ = η̄` and `η⁽ʲ⁺¹⁾ = 1 - θ_j (1 - η⁽ʲ⁾)`. -/
def trialLevel (ηbar : ℝ) (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => ηbar
  | j + 1 => 1 - θ j * (1 - trialLevel ηbar θ j)

/-- The steps visited by the while-loop of Algorithm INB: `s⁽⁰⁾ = s̄` and `s⁽ʲ⁺¹⁾ = θ_j s⁽ʲ⁾`. -/
def trialStep (sbar : E) (θ : ℕ → ℝ) : ℕ → E
  | 0 => sbar
  | j + 1 => θ j • trialStep sbar θ j

/-- Algorithm MR (minimum reduction method, p. 407) without breakdown. Iteration `k` chooses
`η̄_k = ηbar k ∈ [0, η_max]` and a curve `σ k` with (5.1) on `[η̄_k, 1]`; its while-loop runs
`m k` times with factors `θ k j ∈ [θ_min, θ_max]`, every trial level `j < m k` fails (2.2) and the
level `η_k = trialLevel (ηbar k) (θ k) (m k)` passes it; then `x_{k+1} = x_k + σ_k(η_k)`. -/
structure IsMRRun (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (σ : ℕ → ℝ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  ηmax_mem : ηmax ∈ Set.Ico (0 : ℝ) 1
  t_mem : t ∈ Set.Ioo (0 : ℝ) 1
  θ_bounds : 0 < θmin ∧ θmin < θmax ∧ θmax < 1
  ηbar_mem : ∀ k, ηbar k ∈ Set.Icc 0 ηmax
  curve : ∀ k, ∀ η ∈ Set.Icc (ηbar k) 1, InexactNewtonCond F (x k) (σ k η) η
  θ_mem : ∀ k, ∀ j < m k, θ k j ∈ Set.Icc θmin θmax
  rejected : ∀ k, ∀ j < m k,
    ¬ SuffDecrease F t (x k) (σ k (trialLevel (ηbar k) (θ k) j)) (trialLevel (ηbar k) (θ k) j)
  accepted : ∀ k,
    SuffDecrease F t (x k) (σ k (trialLevel (ηbar k) (θ k) (m k))) (trialLevel (ηbar k) (θ k) (m k))
  step : ∀ k, x (k + 1) = x k + σ k (trialLevel (ηbar k) (θ k) (m k))

/-- Algorithm INB (inexact Newton backtracking method, p. 410) without breakdown. Iteration `k`
chooses `η̄_k = ηbar k ∈ [0, η_max]` and an inexact Newton step `s̄_k = sbar k` at level `η̄_k`;
its while-loop runs `m k` times with factors `θ k j ∈ [θ_min, θ_max]`, every trial
`(trialStep (sbar k) (θ k) j, trialLevel (ηbar k) (θ k) j)` with `j < m k` fails (2.2) and the
final one `(s_k, η_k)` (index `m k`) passes it; then `x_{k+1} = x_k + s_k`. -/
structure IsINBRun (F : E → E) (ηmax t θmin θmax : ℝ) (x : ℕ → E) (ηbar : ℕ → ℝ)
    (sbar : ℕ → E) (θ : ℕ → ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  ηmax_mem : ηmax ∈ Set.Ico (0 : ℝ) 1
  t_mem : t ∈ Set.Ioo (0 : ℝ) 1
  θ_bounds : 0 < θmin ∧ θmin < θmax ∧ θmax < 1
  ηbar_mem : ∀ k, ηbar k ∈ Set.Icc 0 ηmax
  initial : ∀ k, InexactNewtonCond F (x k) (sbar k) (ηbar k)
  θ_mem : ∀ k, ∀ j < m k, θ k j ∈ Set.Icc θmin θmax
  rejected : ∀ k, ∀ j < m k,
    ¬ SuffDecrease F t (x k) (trialStep (sbar k) (θ k) j) (trialLevel (ηbar k) (θ k) j)
  accepted : ∀ k,
    SuffDecrease F t (x k) (trialStep (sbar k) (θ k) (m k)) (trialLevel (ηbar k) (θ k) (m k))
  step : ∀ k, x (k + 1) = x k + trialStep (sbar k) (θ k) (m k)

end GlobalInexactNewton.Backtracking


