-- Prove2me | Definitions.Def_BHTOpinion_Approx_Discrete
-- name    : BHTOpinion_Approx_Discrete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:37:50.877256+00:00
-- url     : https://prove2.me/theorems/8e4500d6-a88a-4222-b444-8bf3a1b8d12f
-- title:
--   The discrete-agent opinion model (2.1): solutions and proper solutions
-- statement:
--   This file sets up the discrete-agent opinion model of Blondel, Hendrickx and Tsitsiklis (Section 2), as used in Section 4 of the paper.
--
--   There are $n$ agents; agent $i$ holds the real opinion $x_i(t)$ at time $t\ge 0$. Two agents $i,j$ interact at time $t$ when $|x_i(t)-x_j(t)|<1$ (strict inequality). The interaction term of agent $i$ at the profile $y\in\mathbb R^n$ is
--
--   $$\sum_{j:\,|y_i-y_j|<1}(y_j-y_i).$$
--
--   1. A **solution of the integral equation (2.1)** is a function $x:[0,\infty)\to\mathbb R^n$, continuous on $[0,\infty)$, such that for every $t\ge0$ and every agent $i$
--
--   $$x_i(t)=x_i(0)+\int_0^t\sum_{j:\,|x_i(\tau)-x_j(\tau)|<1}\bigl(x_j(\tau)-x_i(\tau)\bigr)\,d\tau .$$
--
--   2. A solution $x$ is **proper** (its initial value $x(0)$ is a proper initial condition) if (a) every solution of (2.1) with the same initial value coincides with $x$ on $[0,\infty)$; (b) the set of times $t\ge0$ at which $x$ is not differentiable has no accumulation point (hence is at most countable); (c) whenever $x_i(t)=x_j(t)$ for some $t\ge0$, then $x_i(t')=x_j(t')$ for all $t'\ge t$.
--
--   These are the $n$-agent objects of Theorem 7: the sequence of discrete trajectories that approximate the continuum model.
--
--   **Formalization Note** Agents are `Fin n` (0-based). Time is $\mathbb R$ and only times $t\ge0$ enter. The solution predicate requires the integrand to be integrable on $[0,t]$; for a continuous $x$ the integrand is bounded and measurable, so this removes no solution and only rules out Lean's junk value $0$ for a non-integrable integrand. Condition (b) is written as: for every $T$ the set of non-differentiability times in $[0,T]$ is finite, which is equivalent to "no accumulation point in $[0,\infty)$". This file restates, under the namespace `BHTOpinion.Approx`, the definitions of the sibling mission on the discrete model (draft missions cannot import each other's drafts).
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), p. 5214 (1.1), p. 5217 (2.1), p. 5218 (proper initial conditions (a)–(c))

import Mathlib

namespace BHTOpinion.Approx

/-- The right-hand side of (1.1) (p. 5214) at the opinion profile `y : Fin n → ℝ`, for agent `i`:
`∑_{j : |y_i − y_j| < 1} (y_j − y_i)`. The neighbourhood is **strict** (`< 1`) and contains `j = i`,
whose term is `0`. -/
noncomputable def discreteRhs {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => |y i - y j| < 1), (y j - y i)

/-- `x` is a solution of the discrete-agent integral equation (2.1) (p. 5217): `x` is continuous on
`[0, ∞)` and, for every `t ≥ 0` and every agent `i`, the integrand is integrable on `[0, t]` and
`x_i(t) = x_i(0) + ∫_0^t ∑_{j : |x_i(τ) − x_j(τ)| < 1} (x_j(τ) − x_i(τ)) dτ`.
Time is `ℝ`; only the values of `x` at `t ≥ 0` enter. -/
def IsDiscreteSolution {n : ℕ} (x : ℝ → Fin n → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      IntervalIntegrable (fun τ => discreteRhs (x τ) i) MeasureTheory.volume 0 t) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n, x t i = x 0 i + ∫ τ in (0 : ℝ)..t, discreteRhs (x τ) i

/-- `x` is a proper solution of (2.1) (p. 5218): it is a solution and its initial value `x 0` is a
proper initial condition, i.e.
(a) every solution `y` of (2.1) with `y 0 = x 0` coincides with `x` on `[0, ∞)`;
(b) the set of times `t ≥ 0` at which `x` is not differentiable has no accumulation point and is at
most countable, written as: its intersection with every `[0, T]` is finite;
(c) if `x_i(t) = x_j(t)` for some `t ≥ 0`, then `x_i(t') = x_j(t')` for every `t' ≥ t`. -/
def IsProperDiscreteSolution {n : ℕ} (x : ℝ → Fin n → ℝ) : Prop :=
  IsDiscreteSolution x ∧
    (∀ y : ℝ → Fin n → ℝ, IsDiscreteSolution y → y 0 = x 0 → ∀ t : ℝ, 0 ≤ t → y t = x t) ∧
    (∀ T : ℝ, {t : ℝ | t ∈ Set.Icc 0 T ∧ ¬ DifferentiableAt ℝ x t}.Finite) ∧
    (∀ i j : Fin n, ∀ t : ℝ, 0 ≤ t → x t i = x t j → ∀ t' : ℝ, t ≤ t' → x t' i = x t' j)

end BHTOpinion.Approx


