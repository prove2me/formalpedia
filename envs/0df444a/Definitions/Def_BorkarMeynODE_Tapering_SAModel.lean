-- Prove2me | Definitions.Def_BorkarMeynODE_Tapering_SAModel
-- name    : BorkarMeynODE_Tapering_SAModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:38:36.816342+00:00
-- url     : https://prove2.me/theorems/a348d185-ca23-4eea-bd8c-6c4d3ec98022
-- title:
--   The stochastic approximation recursion (1.1) and the martingale-difference noise assumption (A2)
-- statement:
--   Let $(\Omega,\mathcal F,\mathsf P)$ be a probability space, $h:\mathbb R^d\to\mathbb R^d$, and $\{a(n)\}$ a sequence of step sizes. Random sequences $X=\{X(n)\}_{n\ge0}$ and $M=\{M(n)\}_{n\ge0}$ in $\mathbb R^d$ follow the **stochastic approximation recursion** (1.1) if, for every sample point,
--   $$
--   X(n+1) = X(n) + a(n)\big[h(X(n)) + M(n+1)\big], \qquad n\ge0 .
--   $$
--
--   Let $\mathcal F_n = \sigma(X(0),\dots,X(n))$. **Assumption (A2)** with constant $C_0<\infty$ says that for every $n\ge0$:
--
--   1. $M(n+1)$ and $\|M(n+1)\|^2$ are integrable;
--   2. $\mathsf E[M(n+1)\mid\mathcal F_n] = 0$ almost surely ($\{M(n),\mathcal F_n\}$ is a martingale difference sequence);
--   3. the conditional second moment grows at most quadratically:
--   $$
--   \mathsf E\big[\|M(n+1)\|^2 \mid \mathcal F_n\big] \le C_0\big(1+\|X(n)\|^2\big) \quad \text{a.s.}
--   $$
--
--   (A2) is the paper's only condition on the noise; no independence or identical distribution is assumed.
--
--   **Formalization Note** The paper's filtration is $\sigma(X(i),M(i),i\le n)$. Along (1.1) with $a(i)>0$, $M(i) = (X(i)-X(i-1))/a(i-1) - h(X(i-1))$ is a function of $X(i-1),X(i)$ for $i\ge1$, and $M(0)$ enters neither (1.1) nor (A2), so the natural filtration of $X$ (Mathlib's `Filtration.natural`, which needs the iterates to be strongly measurable) carries the same information. The integrability clauses make the conditional expectations meaningful (Lean's conditional expectation of a non-integrable function is $0$); for a deterministic $X(0)$ they follow from the conditional bound by induction.
-- source:
--   Borkar and Meyn, The O.D.E. Method for Convergence of Stochastic Approximation and Reinforcement Learning, SIAM J. Control Optim. 38(2) (2000), p. 447, Eq. (1.1); p. 449, Assumption (A2)

import Mathlib

namespace BorkarMeynODE.Tapering

open MeasureTheory

/-- The stochastic approximation recursion (1.1):
`X(n+1) = X(n) + a(n) [h(X(n)) + M(n+1)]` for all `n ≥ 0`, on every sample point. -/
def IsSARecursion {d : ℕ} {Ω : Type*}
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (a : ℕ → ℝ)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ n ω, X (n + 1) ω = X n ω + a n • (h (X n ω) + M (n + 1) ω)

/-- Assumption (A2) of Borkar–Meyn (p. 449) with constant `C₀`, relative to the natural
filtration `𝓕_n = σ(X(0), …, X(n))` of the (strongly measurable) iterates.

For every `n ≥ 0`: `M(n+1)` and `‖M(n+1)‖²` are integrable, `E[M(n+1) | 𝓕_n] = 0` a.s.
(martingale difference), and `E[‖M(n+1)‖² | 𝓕_n] ≤ C₀ (1 + ‖X(n)‖²)` a.s.

The paper's filtration is `σ(X(i), M(i), i ≤ n)`. Along the recursion (1.1) with `a(i) > 0`,
`M(i) = (X(i) − X(i−1))/a(i−1) − h(X(i−1))` is a function of `X(i−1), X(i)` for `i ≥ 1`, and
`M(0)` enters neither (1.1) nor (A2), so the natural filtration of `X` carries the same
information. The integrability clauses make the conditional expectations meaningful (Lean's
`condExp` of a non-integrable function is `0`); for a deterministic `X(0)` they follow from the
conditional second-moment bound by induction. -/
def AssumptionA2 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X M : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ n, StronglyMeasurable (X n))
    (C₀ : ℝ) : Prop :=
  ∀ n : ℕ,
    Integrable (M (n + 1)) P ∧
    Integrable (fun ω => ‖M (n + 1) ω‖ ^ 2) P ∧
    P[M (n + 1) | Filtration.natural X hX n] =ᵐ[P] 0 ∧
    P[fun ω => ‖M (n + 1) ω‖ ^ 2 | Filtration.natural X hX n]
      ≤ᵐ[P] fun ω => C₀ * (1 + ‖X n ω‖ ^ 2)

end BorkarMeynODE.Tapering


