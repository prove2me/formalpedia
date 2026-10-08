-- Prove2me | Definitions.Def_SAARate_Sharp_Setting
-- name    : SAARate_Sharp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:08.987453+00:00
-- url     : https://prove2.me/theorems/4a803e18-bc38-4fe0-a57a-ed3194db4f1e
-- title:
--   §1–§2, pp. 1–5 — (1.1), (1.2), optimal sets A and A_N, directional derivatives f′, h′_ω, f̂′_N, i.i.d. sample, Assumption (A)
-- statement:
--   This module fixes the objects of Shapiro and Homem-de-Mello's analysis of Monte Carlo (sample average) approximations of a convex stochastic program.
--
--   **The true problem (1.1).** Let $P$ be a probability measure on a sample space $(\Omega,\mathcal F)$, let $\Theta\subseteq\mathbb R^m$ and let $h:\mathbb R^m\times\Omega\to\mathbb R$. The expected value function and the true problem are
--   $$
--   f(x) := \mathbb E_P\, h(x,\omega) = \int_\Omega h(x,\omega)\,P(d\omega),\qquad \min_{x\in\Theta} f(x).
--   $$
--
--   **The approximating problem (1.2).** For an i.i.d. sample $\omega^1,\dots,\omega^N$ drawn from $P$,
--   $$
--   \hat f_N(x) := N^{-1}\sum_{j=1}^N h(x,\omega^j),\qquad \min_{x\in\Theta}\hat f_N(x).
--   $$
--   The sample is the first $N$ terms of one i.i.d. sequence $\omega^1,\omega^2,\dots$ of random elements of $\Omega$, defined on an auxiliary probability space $(S,Q)$: each $\omega^j$ is measurable with law $P$, and the family is mutually independent under $Q$. Here $\hat f_N$ is defined for every sample path $s=(s_1,s_2,\dots)\in\Omega^{\mathbb N}$, and the random function is obtained by inserting the path of the sample.
--
--   **Optimal sets.** For a function $g$ on $\mathbb R^m$, $\operatorname{argmin}_\Theta g=\{x\in\Theta : g(x)\le g(y)\ \forall y\in\Theta\}$. The set $A$ of optimal solutions of (1.1) is $\operatorname{argmin}_\Theta f$, and the optimal set of (1.2) is $\operatorname{argmin}_\Theta \hat f_N$.
--
--   **Directional derivatives.** For $g:\mathbb R^m\to\mathbb R$, $x,d\in\mathbb R^m$,
--   $$
--   g'(x,d) := \lim_{t\downarrow 0}\frac{g(x+td)-g(x)}{t}.
--   $$
--   This gives $f'(x,d)$ (p. 4), $h'_\omega(x,d)$, the directional derivative of $h(\cdot,\omega)$ (p. 5), and $\hat f'_N(x,d)$.
--
--   **Assumption (A)** (p. 4). The true problem (1.1) possesses a unique optimal solution $\bar x$, i.e. $A=\{\bar x\}$, and there is a constant $c>0$ with
--   $$
--   f(x)\ \ge\ f(\bar x)+c\,\|x-\bar x\|\qquad\forall\,x\in\Theta. \tag{2.2}
--   $$
--
--   These objects are shared by every statement of the mission, whose goal is Theorem 2.1: under Assumption (A) and convexity, w.p.1 the approximating problem has the unique optimal solution $\bar x$ for all large $N$.
--
--   **Formalization Note.** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`. The sample is 0-based: the paper's $\omega^j$ is the Lean term `s (j-1)`, and $\hat f_N$ is defined on a sample path. At $N=0$ the factor $N^{-1}$ is Lean's $0^{-1}=0$, so $\hat f_0=0$; only statements about large $N$ use it. The expectation is the Bochner integral, which is $0$ for a non-integrable integrand; every statement using $f$ assumes $h(x,\cdot)$ integrable for every $x$. The directional derivative is the limit `limUnder` along $t\downarrow0$; it has an unspecified value when the one-sided limit does not exist, so every statement using it assumes the function convex and finite on $\mathbb R^m$, where the limit exists. Optimal sets are defined without any infimum.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), pp. 1–5, (1.1), (1.2) p. 1, A, f′(x, d), "w.p.1 for N large enough" and Assumption (A), (2.2) p. 4, h′_ω(x, d) p. 5

import Mathlib

namespace SAARate.Sharp

open MeasureTheory ProbabilityTheory Filter Topology

/-- The decision space `ℝ^m` of (1.1), with the Euclidean norm. -/
abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The expected value function `f(x) = E_P h(x, ω) = ∫ h(x, ω) dP(ω)` of (1.1), p. 1.
It is the Bochner integral, which Lean sets to `0` when `h(x, ·)` is not integrable; every
statement using it assumes `∀ x, Integrable (h x) P` (Theorem 2.1 (ii)). -/
noncomputable def expectedObj {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : E m → Ω → ℝ) (x : E m) : ℝ :=
  ∫ ω, h x ω ∂P

/-- The sample average function `f̂_N(x) = N⁻¹ Σ_{j=1}^N h(x, ωʲ)` of (1.2), p. 1, evaluated on a
sample path `s`: the paper's `ωʲ` is `s (j - 1)`. At `N = 0` it is `0`. -/
noncomputable def saaObj {m : ℕ} {Ω : Type*} (h : E m → Ω → ℝ) (s : ℕ → Ω) (N : ℕ)
    (x : E m) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h x (s j)

/-- The set of optimal solutions `{x ∈ Θ : g(x) ≤ g(y) ∀ y ∈ Θ}` of `min_{x ∈ Θ} g(x)`: the set
`A` (p. 4) for `g = f`, and the optimal set of (1.2) for `g = f̂_N`. -/
def argminOn {m : ℕ} (g : E m → ℝ) (Θ : Set (E m)) : Set (E m) :=
  {x | x ∈ Θ ∧ ∀ y ∈ Θ, g x ≤ g y}

/-- The directional derivative `g′(x, d) = lim_{t ↓ 0} (g(x + t d) − g(x)) / t` (p. 4, p. 5), as a
value. Lean's `limUnder` returns an unspecified value when the one-sided limit does not exist;
every statement using it assumes `g` convex and finite on `ℝ^m`, where the limit exists. -/
noncomputable def dirDeriv {m : ℕ} (g : E m → ℝ) (x d : E m) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun t => (g (x + t • d) - g x) / t)

/-- `ω 0, ω 1, …` is an i.i.d. sample from `P`, defined on the probability space `(S, Q)`: each
`ω j` is measurable, the family is mutually independent under `Q`, and each `ω j` has law `P`.
The paper's sample `ω¹, …, ω^N` is `ω 0, …, ω (N - 1)`, the first `N` terms of one sequence. -/
def IsIIDSample {Ω : Type*} [MeasurableSpace Ω] {S : Type*} [MeasurableSpace S] (Q : Measure S)
    (P : Measure Ω) (ω : ℕ → S → Ω) : Prop :=
  (∀ j, Measurable (ω j)) ∧ iIndepFun ω Q ∧ ∀ j, Q.map (ω j) = P

/-- Assumption (A), p. 4: `x̄ ∈ Θ`, the true problem (1.1) has the unique optimal solution `x̄`
(`A = {x̄}`), and there is `c > 0` with `f(x) ≥ f(x̄) + c ‖x − x̄‖` for all `x ∈ Θ` (2.2). -/
structure AssumptionA {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : E m → Ω → ℝ) (Θ : Set (E m)) (xbar : E m) : Prop where
  mem : xbar ∈ Θ
  unique : argminOn (expectedObj P h) Θ = {xbar}
  sharp : ∃ c > 0, ∀ x ∈ Θ, expectedObj P h x ≥ expectedObj P h xbar + c * ‖x - xbar‖

end SAARate.Sharp


