-- Prove2me | Definitions.Def_NonsmoothQN_Secant_Basic
-- name    : NonsmoothQN_Secant_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:10.035986+00:00
-- url     : https://prove2.me/theorems/80c44b2f-8d29-42b3-a3ad-3d380cfe4d6b
-- title:
--   Algorithm 4.6, §5.1 and §2, pp. 141, 147, 151 — bisection line search, the secant method on |x|, its trial points, Q- and R-linear rates
-- statement:
--   This file fixes the objects of §5.1 of Lewis and Overton: the secant method (the quasi-Newton method in dimension one) applied to $f(x)=|x|$ with the bisection line search, together with the convergence rates of §2.
--
--   **The line search (Algorithm 4.6).** Given an *Armijo test* $A$ and a *Wolfe test* $W$ on steps $t>0$, the line search keeps a bracket $[\alpha,\beta]$ with $\alpha\leftarrow 0$, $\beta\leftarrow+\infty$ and first trial step $t\leftarrow 1$. One *trial* tests the current $t$: if $A(t)$ fails it sets $\beta\leftarrow t$; otherwise, if $W(t)$ fails, it sets $\alpha\leftarrow t$; otherwise it stops and returns $t$. After an update the next step is $t\leftarrow(\alpha+\beta)/2$ if $\beta<+\infty$ and $t\leftarrow 2\alpha$ otherwise. The line search *terminates* if some trial passes both tests; its *number of trials* counts the stopping trial.
--
--   **The tests of §5.1.** At an iterate $x$ with search direction $p$ (where $px<0$) the line search objective is $h(t)=|x+tp|-|x|$, the Armijo parameter is $c_1=0$, and the two conditions become
--   $$A(t):\ t<-\frac{2x}{p},\qquad W(t):\ t\ge-\frac{x}{p}.$$
--
--   **The secant method.** Start from $x_0$ and $H_0$. At step $k$, if $x_k=0$ the method has stopped. Otherwise the direction is $p_k=-H_k\operatorname{sgn}(x_k)$, the step $t_k$ is the one returned by the line search above at $(x_k,p_k)$, and $x_{k+1}=x_k+t_kp_k$. If $x_{k+1}=0$ (that is, $t_k=-x_k/p_k$) the method terminates at zero. Otherwise $H_{k+1}$ is the unique solution of the secant equation $H_{k+1}y_k=t_kp_k$ with $y_k=\operatorname{sgn}(x_{k+1})-\operatorname{sgn}(x_k)$. We write $N_k$ for the number of trials of the $k$-th line search (the one producing $x_{k+1}$), $\nu_k=N_0+\dots+N_{k-1}$, and $z_0,z_1,z_2,\dots$ for all trial points $x_k+tp_k$ of all line searches in the order they are tried, so that the $i$-th trial of the $k$-th line search is $z_{\nu_k+i}$. The *function trial values* are $|z_j|$.
--
--   **Rates (§2, p. 141).** A sequence $\tau_k\to\mu$ converges *Q-linearly with rate $r$* if
--   $$\lim_{k\to\infty}\frac{|\tau_{k+1}-\mu|}{|\tau_k-\mu|}=r .$$
--   A sequence $\upsilon_k$ converges *R-linearly with rate $r$* if $|\upsilon_k-\mu|\le|\tau_k-\mu|$ for all $k$, for some sequence $\tau_k$ converging to $\mu$ Q-linearly with rate $r$.
--
--   These objects are shared by every statement of the mission: the trial counts and the trial values are those of the algorithm itself, not of a closed form for its output.
--
--   **Formalization Note** Algorithm 4.6 is the iteration `lsRun A W` on states $(\alpha,\beta,t)$ with $\beta\in$ `WithTop ℝ` ($\top=+\infty$); state $n$ holds the step of the $(n+1)$-st trial. The stopping index is the least $n$ at which both tests hold (`sInf`, which is $0$ if the line search never stops; the number of trials is then meaningless, so statements about trials also assert termination). The §5.1 replacement of the differentiability check by a termination condition is the freezing of the run at $x_k=0$. At a frozen or terminal step $H$ is kept unchanged and never used again; the division in $H_{k+1}$ is only meaningful when the signs of $x_k$ and $x_{k+1}$ differ, which the line search guarantees. In Q-linear convergence the ratio $|\tau_{k+1}-\mu|/|\tau_k-\mu|$ is required to be defined, i.e. $\tau_k\ne\mu$ for all $k$. Indices start at $0$ as in the paper. This line search is a copy of the one in the companion mission on §4 of the paper, specialized to no oracle beyond the two tests.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 140 Algorithm 2.1, p. 141 (Q-/R-linear), p. 147 Algorithm 4.6, p. 151 §5.1 (A(t), W(t))

import Mathlib

namespace NonsmoothQN.Secant

open Filter Topology

/-- State of the line search Algorithm 4.6 (p. 147) between two trials: the lower bound `α`,
the upper bound `β` (`⊤` stands for `+∞`), and the next trial step `t`. -/
structure LSState where
  α : ℝ
  β : WithTop ℝ
  t : ℝ

/-- One execution of the repeat loop of Algorithm 4.6 (one *trial*) with Armijo test `A` and
Wolfe test `W`: if `A(t)` fails, `β ← t`; else if `W(t)` fails, `α ← t`; else the loop stops
(the state is left unchanged). Then `t ← (α + β)/2` if `β < +∞`, and `t ← 2α` otherwise. -/
noncomputable def lsStep (A W : ℝ → Prop) (s : LSState) : LSState := by
  classical
  exact
    if ¬ A s.t then
      { α := s.α, β := (s.t : WithTop ℝ), t := (s.α + s.t) / 2 }
    else if ¬ W s.t then
      match s.β with
      | ⊤ => { α := s.t, β := ⊤, t := 2 * s.t }
      | (b : ℝ) => { α := s.t, β := (b : WithTop ℝ), t := (s.t + b) / 2 }
    else s

/-- The states of Algorithm 4.6: `lsRun A W 0 = (α, β, t) = (0, +∞, 1)`, and
`(lsRun A W n).t` is the step tried at the `(n+1)`-st trial. -/
noncomputable def lsRun (A W : ℝ → Prop) : ℕ → LSState
  | 0 => { α := 0, β := ⊤, t := 1 }
  | n + 1 => lsStep A W (lsRun A W n)

/-- Algorithm 4.6 terminates: some trial step satisfies both `A` and `W`. -/
def lsTerminates (A W : ℝ → Prop) : Prop :=
  ∃ n : ℕ, A (lsRun A W n).t ∧ W (lsRun A W n).t

/-- Index of the stopping trial (`0`-based): the first `n` at which both tests hold. -/
noncomputable def lsStopIndex (A W : ℝ → Prop) : ℕ :=
  sInf {n : ℕ | A (lsRun A W n).t ∧ W (lsRun A W n).t}

/-- The step returned by Algorithm 4.6 (its final trial step). -/
noncomputable def lsResult (A W : ℝ → Prop) : ℝ :=
  (lsRun A W (lsStopIndex A W)).t

/-- The number of trials taken by Algorithm 4.6 (the stopping trial included). -/
noncomputable def lsTrials (A W : ℝ → Prop) : ℕ :=
  lsStopIndex A W + 1

/-- The Armijo condition of §5.1 (p. 151) at the iterate `x` with direction `p`:
`A(t) : t < -2x/p`. -/
def secA (x p t : ℝ) : Prop := t < -2 * x / p

/-- The Wolfe condition of §5.1 (p. 151) at the iterate `x` with direction `p`:
`W(t) : t ≥ -x/p`. -/
def secW (x p t : ℝ) : Prop := -x / p ≤ t

/-- State of the secant method (Algorithm 2.1 with `n = 1`, `f = |·|`): iterate `x` and inverse
Hessian approximation `H`. -/
structure SecState where
  x : ℝ
  H : ℝ

/-- Search direction `p = -H ∇f(x) = -H sgn(x)`. -/
noncomputable def secDir (s : SecState) : ℝ := -s.H * Real.sign s.x

/-- The step `t` returned by the inexact line search (Algorithm 4.6 with the §5.1 tests). -/
noncomputable def secStepSize (s : SecState) : ℝ :=
  lsResult (secA s.x (secDir s)) (secW s.x (secDir s))

/-- One iteration of the secant method. At `x = 0` the method has stopped and the state is
frozen. Otherwise `x⁺ = x + t p`; if `x⁺ = 0` the method terminates (the state keeps `H`, which
is never used again); else `H⁺` solves the secant equation `H⁺ y = t p` with
`y = sgn(x⁺) - sgn(x)`. -/
noncomputable def secStep (s : SecState) : SecState := by
  classical
  exact
    if s.x = 0 then s
    else
      if s.x + secStepSize s * secDir s = 0 then
        { x := s.x + secStepSize s * secDir s, H := s.H }
      else
        { x := s.x + secStepSize s * secDir s,
          H := secStepSize s * secDir s /
            (Real.sign (s.x + secStepSize s * secDir s) - Real.sign s.x) }

/-- The secant method started at `x₀` with `H₀`. -/
noncomputable def secRun (x₀ H₀ : ℝ) : ℕ → SecState
  | 0 => { x := x₀, H := H₀ }
  | k + 1 => secStep (secRun x₀ H₀ k)

/-- The iterate `x_k`. -/
noncomputable def secX (x₀ H₀ : ℝ) (k : ℕ) : ℝ := (secRun x₀ H₀ k).x

/-- The inverse Hessian approximation `H_k`. -/
noncomputable def secH (x₀ H₀ : ℝ) (k : ℕ) : ℝ := (secRun x₀ H₀ k).H

/-- The search direction `p_k = -H_k sgn(x_k)`. -/
noncomputable def secP (x₀ H₀ : ℝ) (k : ℕ) : ℝ := secDir (secRun x₀ H₀ k)

/-- The step `t_k` returned by the `k`-th line search. -/
noncomputable def secT (x₀ H₀ : ℝ) (k : ℕ) : ℝ := secStepSize (secRun x₀ H₀ k)

/-- The `k`-th line search (the one computing `x_{k+1}` from `x_k`) terminates. -/
def secLSTerminates (x₀ H₀ : ℝ) (k : ℕ) : Prop :=
  lsTerminates (secA (secX x₀ H₀ k) (secP x₀ H₀ k)) (secW (secX x₀ H₀ k) (secP x₀ H₀ k))

/-- `N_k`: the number of trials of the `k`-th line search. -/
noncomputable def secTrials (x₀ H₀ : ℝ) (k : ℕ) : ℕ :=
  lsTrials (secA (secX x₀ H₀ k) (secP x₀ H₀ k)) (secW (secX x₀ H₀ k) (secP x₀ H₀ k))

/-- The `i`-th trial point `x_k + t p_k` of the `k`-th line search (`i` is `0`-based). -/
noncomputable def secTrialPoint (x₀ H₀ : ℝ) (k i : ℕ) : ℝ :=
  secX x₀ H₀ k +
    (lsRun (secA (secX x₀ H₀ k) (secP x₀ H₀ k)) (secW (secX x₀ H₀ k) (secP x₀ H₀ k)) i).t *
      secP x₀ H₀ k

/-- `ν_k = N_0 + ⋯ + N_{k-1}`: the number of trials of the first `k` line searches. -/
noncomputable def secNu (x₀ H₀ : ℝ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, secTrials x₀ H₀ i

/-- The line search that the `j`-th trial overall (`0`-based) belongs to. -/
noncomputable def secLSIndex (x₀ H₀ : ℝ) (j : ℕ) : ℕ :=
  sInf {k : ℕ | j < secNu x₀ H₀ (k + 1)}

/-- The `j`-th trial point overall (`0`-based): the trial points of all line searches, in the
order in which they are tried. The function trial values are `|allTrial x₀ H₀ j|`. -/
noncomputable def allTrial (x₀ H₀ : ℝ) (j : ℕ) : ℝ :=
  secTrialPoint x₀ H₀ (secLSIndex x₀ H₀ j) (j - secNu x₀ H₀ (secLSIndex x₀ H₀ j))

/-- Q-linear convergence (p. 141): `τ_k → μ` and `|τ_{k+1} - μ| / |τ_k - μ| → r`
(the ratios are required to be defined, i.e. `τ_k ≠ μ`). -/
def IsQLinear (τ : ℕ → ℝ) (μ r : ℝ) : Prop :=
  (∀ k, τ k ≠ μ) ∧ Tendsto τ atTop (𝓝 μ) ∧
    Tendsto (fun k => |τ (k + 1) - μ| / |τ k - μ|) atTop (𝓝 r)

/-- R-linear convergence (p. 141): `|υ_k - μ| ≤ |τ_k - μ|` for all `k`, for some sequence `τ`
converging to `μ` Q-linearly with rate `r`. -/
def IsRLinear (υ : ℕ → ℝ) (μ r : ℝ) : Prop :=
  ∃ τ : ℕ → ℝ, IsQLinear τ μ r ∧ ∀ k, |υ k - μ| ≤ |τ k - μ|

end NonsmoothQN.Secant


