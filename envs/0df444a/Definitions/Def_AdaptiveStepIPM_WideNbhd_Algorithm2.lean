-- Prove2me | Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2
-- name    : AdaptiveStepIPM_WideNbhd_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:47.225296+00:00
-- url     : https://prove2.me/theorems/87f83528-8dec-4551-9b03-4e537525f8a8
-- title:
--   The search direction (2), the scaled vectors $p, q, r$ (6), and one iteration of Algorithm 2
-- statement:
--   Let $A,b,c$ be the data of the linear program (P)–(D), $x,s\in\mathbb R^n$ with $x,s>0$, $\mu = x^Ts/n$, $X=\operatorname{diag}(x)$, $S=\operatorname{diag}(s)$, $e=(1,\dots,1)^T$, and let $\gamma$ be a centering parameter.
--
--   1. **Search direction (2).** A triple $(d_x,d_y,d_s)$ solves system (2) at $(x,s)$ with parameter $\gamma$ if
--   $$
--   S d_x + X d_s = \gamma\mu e - Xs,\qquad A d_x = 0,\qquad A^Td_y + d_s = 0 .
--   $$
--   2. **Scaled vectors (6).** $p = X^{-1/2}S^{1/2}d_x$, $q = X^{1/2}S^{-1/2}d_s$, $r = (XS)^{-1/2}(\gamma\mu e - Xs)$, that is $p_j=\sqrt{s_j/x_j}\,(d_x)_j$, $q_j = \sqrt{x_j/s_j}\,(d_s)_j$, $r_j = (\gamma\mu - x_js_j)/\sqrt{x_js_j}$; and $Pq = (p_jq_j)_j$ with $P=\operatorname{diag}(p)$, which equals $D_xd_s$ by (8).
--   3. **Step (3).** $x(\theta) = x+\theta d_x$, $s(\theta) = s+\theta d_s$.
--   4. **Admissible steps.** For a set $\mathcal N$ of pairs, the admissible step lengths are the $\bar\theta\ge0$ with $(x(\theta),s(\theta))\in\mathcal N$ for all $\theta\in[0,\bar\theta]$.
--   5. **One iteration of Algorithm 2** with neighbourhood $\mathcal N$ and parameter $\gamma$ takes $(x,s)$ to $(x^+,s^+) = (x(\bar\theta),s(\bar\theta))$, where $d$ solves (2) and $\bar\theta$ is the **largest** admissible step length.
--   6. **Step bound.** For reals $\beta,\gamma,\mu,\nu$, $\min\{1,\beta\gamma\mu/\nu\}$, read as $1$ when $\nu=0$. With $\nu = \|Pq\|_\infty$ this is $\theta_2$ of Lemma 5; with $\nu = \|Pq\|^-_\infty$ it is $\theta_2^-$.
--
--   Algorithm 2 (§4) starts from $(x^0,s^0)\in\mathcal N$ with $(x^0)^Ts^0\le 2^t$ and repeats this iteration while $(x^k)^Ts^k > 2^{-t}$.
--
--   **Formalization Note** The direction is "any solution of (2)"; no rank assumption on $A$ is made ($(d_x,d_s)$ is unique for $x,s>0$ in any case). "The largest $\bar\theta$" is encoded with `IsGreatest`: when the admissible set has no maximum (for example $n=1$, where $Pq = 0$ and the admissible set is $[0,1/(1-\gamma))$), there is no iteration, and the algorithm has no run from that point. $\bar\theta$ is not capped at $1$. Lean's real division returns $0$ on a zero denominator, so the case $\nu=0$ of the step bound (where the paper's quotient is $+\infty$) is defined explicitly as $1$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 4–5, (2), (3), (6), (8); pp. 9–10, Algorithm 2 and Lemma 5 (θ₂, θ₂⁻)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

namespace AdaptiveStepIPM.WideNbhd

open Matrix

/-- `(d_x, d_y, d_s)` solves system (2) of §2, p. 4, at `(x, s)` with centering parameter `γ`:
`S d_x + X d_s = γμe − Xs`, `A d_x = 0`, `Aᵀ d_y + d_s = 0`, where `μ = xᵀs/n`. -/
def IsDirection {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) ∧ A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- `p := X^{-0.5} S^{0.5} d_x`, i.e. `p_j = √(s_j / x_j) (d_x)_j` ((6), p. 4). -/
noncomputable def pvec {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- `q := X^{0.5} S^{-0.5} d_s`, i.e. `q_j = √(x_j / s_j) (d_s)_j` ((6), p. 4). -/
noncomputable def qvec {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- `r := (XS)^{-0.5}(γμe − Xs)`, i.e. `r_j = (γμ − x_j s_j) / √(x_j s_j)` ((6), p. 4). -/
noncomputable def rvec {n : ℕ} (γ : ℝ) (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (γ * AdaptiveStepIPM.PredCorr.mu x s - x j * s j) / Real.sqrt (x j * s j)

/-- The admissible step lengths of Algorithm 2 (§4, p. 9): the `θ̄ ≥ 0` such that
`(x(θ), s(θ)) = (x + θ d_x, s + θ d_s) ∈ N` for every `θ ∈ [0, θ̄]` ((3), p. 4). -/
def admissibleSteps {n : ℕ} (N : Set ((Fin n → ℝ) × (Fin n → ℝ))) (x s dx ds : Fin n → ℝ) :
    Set ℝ :=
  {θbar | 0 ≤ θbar ∧ ∀ θ ∈ Set.Icc (0 : ℝ) θbar, (x + θ • dx, s + θ • ds) ∈ N}

/-- One iteration of Algorithm 2 (§4, pp. 9–10) with neighbourhood `N` and parameter `γ`:
from `(x, s)`, take a solution `d` of (2), the largest `θ̄` with `(x(θ), s(θ)) ∈ N` for all
`θ ∈ [0, θ̄]`, and move to `(x⁺, s⁺) = (x(θ̄), s(θ̄))`. -/
def Alg2Step {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (N : Set ((Fin n → ℝ) × (Fin n → ℝ)))
    (γ : ℝ) (x s x' s' : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ),
    IsDirection A x s γ dx dy ds ∧ IsGreatest (admissibleSteps N x s dx ds) θbar ∧
    x' = x + θbar • dx ∧ s' = s + θbar • ds

/-- The step bound `min{1, βγμ / ν}` of Lemma 5 (p. 10), with `ν = ‖AdaptiveStepIPM.PredCorr.Pq‖_∞` (giving `θ₂`) or
`ν = ‖AdaptiveStepIPM.PredCorr.Pq‖⁻_∞` (giving `θ₂⁻`). When `ν = 0` the quotient is `+∞` and the minimum is `1`; this
case is made explicit because Lean's real division by zero returns `0`. -/
noncomputable def stepBound (β γ μ ν : ℝ) : ℝ :=
  if ν = 0 then 1 else min 1 (β * γ * μ / ν)

end AdaptiveStepIPM.WideNbhd


