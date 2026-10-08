-- Prove2me | Definitions.Def_BHTOpinion_Discrete_Model
-- name    : BHTOpinion_Discrete_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:11.867001+00:00
-- url     : https://prove2.me/theorems/940332b9-fb95-4179-a1a6-4b1f08f150a5
-- title:
--   The n-agent opinion model of Section 2: the integral equation (2.1), proper solutions (a)–(c), the equilibria F, the average and V
-- statement:
--   This file sets up the discrete-agent opinion model of Blondel, Hendrickx and Tsitsiklis (Sections 1–2.1).
--
--   **Agents and the interaction rule.** There are $n$ agents, each holding a real opinion $x_i(t)$ at time $t\ge 0$; an opinion profile is a vector $y\in\mathbb R^n$. Agent $j$ is a **neighbour** of agent $i$ when $|y_i-y_j|<1$ (strict inequality; $i$ is its own neighbour). The right-hand side of the differential equation (1.1) is
--
--   $$r_i(y)=\sum_{j:\,|y_i-y_j|<1}\bigl(y_j-y_i\bigr).$$
--
--   **Solutions of (2.1).** Because $r$ jumps when the neighbour relation changes, the model is the integral equation (2.1). A trajectory $x:[0,\infty)\to\mathbb R^n$ is a **solution of (2.1)** if it is continuous and, for every $t\ge 0$ and every agent $i$,
--
--   $$x_i(t)=x_i(0)+\int_0^t\sum_{j:\,|x_i(\tau)-x_j(\tau)|<1}\bigl(x_j(\tau)-x_i(\tau)\bigr)\,d\tau .$$
--
--   **Proper solutions.** A solution $x$ is **proper** if its initial value $\tilde x=x(0)$ is a proper initial condition, that is:
--
--   1. (a) $x$ is the only solution of (2.1) with $x(0)=\tilde x$;
--   2. (b) the set of times $t\ge0$ at which $x$ is not differentiable is at most countable and has no accumulation point;
--   3. (c) if $x_i(t)=x_j(t)$ for some $t\ge0$, then $x_i(t')=x_j(t')$ for every $t'\ge t$.
--
--   **Equilibria.** $F$ is the set of vectors $\tilde s\in\mathbb R^n$ such that for all agents $i,j$, either $\tilde s_i=\tilde s_j$ or $|\tilde s_i-\tilde s_j|\ge 1$ (non-strict).
--
--   **Average and variance.** For $y\in\mathbb R^n$, $\bar y=\frac1n\sum_{i=1}^n y_i$ and $V(y)=\sum_{i=1}^n (y_i-\bar y)^2$.
--
--   These objects are shared by every statement of the mission: order preservation, Proposition 1, the monotone partial sums (2.3), and the convergence Theorem 2.
--
--   **Formalization Note** Agents are indexed by `Fin n` (the paper's $1,\dots,n$ shifted to $0,\dots,n-1$); time is $\mathbb R$ and only values at $t\ge 0$ enter (continuity is `ContinuousOn` on $[0,\infty)$, the equation is required for $t\ge 0$, and uniqueness in (a) is agreement on $[0,\infty)$). The solution predicate also requires the integrand to be interval-integrable on $[0,t]$; for a continuous trajectory the integrand is bounded and measurable, so this removes no solution and only excludes Lean's junk value $0$ for non-integrable integrands. Uniqueness (a) is among all such solutions, not among sorted or differentiable ones. Condition (b) is written as: for every $T$, the non-differentiability times in $[0,T]$ form a finite set; for a subset of $[0,\infty)$ this is equivalent to being at most countable with no accumulation point. Differentiability at $t=0$ is two-sided in Lean, which affects only the single point $0$ and hence not finiteness. $\bar y$ is defined with the factor $1/n$, which is $0$ when $n=0$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Eq. (1.1) p. 5214; Eq. (2.1) p. 5217; proper initial conditions (a)–(c), the set F, and Proposition 1 (x̄, V), p. 5218

import Mathlib

namespace BHTOpinion.Discrete

/-- The right-hand side of (1.1) (p. 5214) at the opinion profile `y : Fin n → ℝ`, for agent `i`:
`∑_{j : |y_i − y_j| < 1} (y_j − y_i)`. The neighbourhood is **strict** (`< 1`) and contains `j = i`,
whose term is `0`. -/
noncomputable def rhs {n : ℕ} (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => |y i - y j| < 1), (y j - y i)

/-- `x` is a solution of the integral equation (2.1) (p. 5217): `x` is continuous on `[0, ∞)` and,
for every `t ≥ 0` and every agent `i`, the integrand is integrable on `[0, t]` and
`x_i(t) = x_i(0) + ∫_0^t ∑_{j : |x_i(τ) − x_j(τ)| < 1} (x_j(τ) − x_i(τ)) dτ`.
(For `x` continuous the integrand is bounded and measurable on `[0, t]`, so the integrability
clause removes no solution; it only rules out Lean's junk value `0` for a non-integrable integrand.)
Time is `ℝ`; only the values of `x` at `t ≥ 0` enter. -/
def IsSolution {n : ℕ} (x : ℝ → Fin n → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      IntervalIntegrable (fun τ => rhs (x τ) i) MeasureTheory.volume 0 t) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n, x t i = x 0 i + ∫ τ in (0 : ℝ)..t, rhs (x τ) i

/-- `x` is a proper solution of (2.1) (p. 5218): it is a solution and its initial value `x 0` is a
proper initial condition, i.e.
(a) every solution `y` of (2.1) with `y 0 = x 0` coincides with `x` on `[0, ∞)`;
(b) the set of times `t ≥ 0` at which `x` is not differentiable has no accumulation point and is at
most countable, written as: its intersection with every `[0, T]` is finite;
(c) if `x_i(t) = x_j(t)` for some `t ≥ 0`, then `x_i(t') = x_j(t')` for every `t' ≥ t`. -/
def IsProperSolution {n : ℕ} (x : ℝ → Fin n → ℝ) : Prop :=
  IsSolution x ∧
    (∀ y : ℝ → Fin n → ℝ, IsSolution y → y 0 = x 0 → ∀ t : ℝ, 0 ≤ t → y t = x t) ∧
    (∀ T : ℝ, {t : ℝ | t ∈ Set.Icc 0 T ∧ ¬ DifferentiableAt ℝ x t}.Finite) ∧
    (∀ i j : Fin n, ∀ t : ℝ, 0 ≤ t → x t i = x t j → ∀ t' : ℝ, t ≤ t' → x t' i = x t' j)

/-- The set `F` of equilibria (p. 5218): vectors `s` such that for all agents `i, j`, either
`s_i = s_j` or `|s_i − s_j| ≥ 1` (non-strict). -/
def F (n : ℕ) : Set (Fin n → ℝ) :=
  {s | ∀ i j : Fin n, s i = s j ∨ 1 ≤ |s i - s j|}

/-- The average opinion `ȳ = (1/n) ∑_i y_i` (Proposition 1, p. 5218). -/
noncomputable def avg {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, y i

/-- The sum of squared differences from the average, `V(y) = ∑_i (y_i − ȳ)²`
(Proposition 1, p. 5218). -/
noncomputable def V {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ i, (y i - avg y) ^ 2

end BHTOpinion.Discrete


