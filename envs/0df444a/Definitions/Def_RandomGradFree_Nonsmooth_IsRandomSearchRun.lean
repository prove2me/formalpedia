-- Prove2me | Definitions.Def_RandomGradFree_Nonsmooth_IsRandomSearchRun
-- name    : RandomGradFree_Nonsmooth_IsRandomSearchRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:14:38.364382+00:00
-- url     : https://prove2.me/theorems/4eaf6c51-f372-43e4-9873-ecebe74524ff
-- title:
--   A run of the random search method $\mathcal{RS}_\mu$ (Eq. (39))
-- statement:
--   Fix a set $Q \subseteq E$, a function $f : E \to \mathbb R$, a smoothing parameter $\mu$, step sizes $(h_k)_{k \ge 0}$ and a starting point $x_0$. A **run of the random search method $\mathcal{RS}_\mu$** on a probability space $(\Omega, P)$ consists of random directions $u_0, u_1, \dots : \Omega \to E$ and random iterates $x_0, x_1, \dots : \Omega \to E$ such that
--
--   1. the directions $u_k$ are measurable, mutually independent, and each has the standard Gaussian law on $E$;
--   2. the starting point $x_0$ lies in $Q$ and is deterministic;
--   3. for every $k \ge 0$ and every outcome,
--   $$
--   x_{k+1} = \pi_Q\!\left(x_k - h_k B^{-1} g_\mu(x_k)\right), \qquad B^{-1}g_\mu(x_k) = \frac{f(x_k+\mu u_k)-f(x_k)}{\mu}\, u_k .
--   $$
--
--   This is the method of the paper: at each iteration generate $u_k$ and the corresponding oracle value, then take a projected step.
--
--   **Formalization Note** Independence is Mathlib's `iIndepFun` of the sequence $(u_k)$ under $P$, and the law condition is `P.map (u k) = stdGaussian E`. The projection is the relation `IsMetricProjection`. Positivity of the steps and the hypotheses on $Q$ and $f$ are stated in the theorems that use a run.
-- source:
--   Nesterov, Spokoiny, Random Gradient-Free Minimization of Convex Functions, Found. Comput. Math. 17 (2017), p. 541, Section 4, Method RS_μ (39) and the paragraph after it

import Mathlib
import Definitions.Def_RandomGradFree_Nonsmooth_oracle
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection

namespace RandomGradFree.Nonsmooth

open MeasureTheory ProbabilityTheory

/-- A run of the random search method `RS_μ` (Nesterov–Spokoiny, Eq. (39), p. 541) on the
probability space `(Ω, P)`: the directions `u k` are independent, each a measurable random
vector with the standard Gaussian law on `E`; the starting point `x₀` lies in `Q`; and for
every `k` and every outcome `ω`, `x (k+1) ω = π_Q(x_k - h_k B⁻¹ g_μ(x_k))`, where the oracle is
evaluated at the direction `u k ω`. -/
structure IsRandomSearchRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : Set E) (f : E → ℝ) (μ : ℝ) (h : ℕ → ℝ) (x₀ : E)
    (u : ℕ → Ω → E) (x : ℕ → Ω → E) : Prop where
  measurable_dir : ∀ k, Measurable (u k)
  indep_dir : iIndepFun u P
  law_dir : ∀ k, P.map (u k) = stdGaussian E
  start_mem : x₀ ∈ Q
  init : x 0 = fun _ => x₀
  step : ∀ k ω, IsMetricProjection Q (x k ω - h k • oracle f μ (x k ω) (u k ω)) (x (k + 1) ω)

end RandomGradFree.Nonsmooth


