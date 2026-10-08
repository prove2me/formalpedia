-- Prove2me | Definitions.Def_RobbinsSeqDesign_OptionalStopping_Setup
-- name    : RobbinsSeqDesign_OptionalStopping_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:48.316991+00:00
-- url     : https://prove2.me/theorems/f9dffb58-e38a-4358-89f5-6e0a0508575d
-- title:
--   Section 4, (23)–(24): the normal distribution function Φ, the partial sums S_n and the window probability g(n₁, n₂, α)
-- statement:
--   This file fixes the three objects of Section 4 of Robbins (1952), "The problem of optional stopping".
--
--   1. **The standard normal distribution function** of (23),
--   $$
--   \Phi(x)=\frac{1}{(2\pi)^{1/2}}\int_{-\infty}^{x}e^{-t^2/2}\,dt ,\qquad x\in\mathbb R .
--   $$
--   2. **The partial sums.** Given a sequence of real random variables $x_1,x_2,\dots$ on a probability space $(\Omega,\mathcal F,P)$, put
--   $$
--   S_n=x_1+\cdots+x_n ,\qquad S_0=0 .
--   $$
--   3. **The window probability** of (24): for integers $n_1\le n_2$ and a real constant $\alpha$,
--   $$
--   g(n_1,n_2,\alpha)=P\bigl[\,S_n>\alpha n^{1/2}\ \text{for some } n \text{ with } n_1\le n\le n_2\,\bigr],
--   $$
--   the probability that the fixed-sample test "reject $H_0$ when $S_n>\alpha n^{1/2}$" of (21) rejects at some sample size in the window $\{n_1,\dots,n_2\}$, both endpoints included.
--
--   These are the objects in which the fixed-sample error probability (22) and the optional-stopping bound (25) are stated. The letter $\alpha$ is the test constant of (21), not the coin mean of the paper's Section 2.
--
--   **Formalization Note.** $\Phi$ is written as the integral printed in (23), as a Bochner integral over $(-\infty,x]$; the integrand is integrable, so no default value occurs, and a local check shows that it equals Mathlib's `cdf (gaussianReal 0 1)`. The observations are indexed from $0$: the paper's $x_i$ is `X (i - 1)`, so `S X n ω = X 0 ω + ⋯ + X (n-1) ω`. The probability $g$ is `P.real` of the event, a real number in $[0,1]$ when $P$ is a probability measure. The paper prints "for some $n_1, \le n\le n_2$" with a stray comma; the window is read as $n_1\le n\le n_2$.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), pp. 534–535, Section 4, Eqs. (23), (24)

import Mathlib

namespace RobbinsSeqDesign.OptionalStopping

open MeasureTheory

/-- The standard normal distribution function of (23), written as printed:
`Φ(x) = (2π)^{-1/2} ∫_{-∞}^{x} e^{-t²/2} dt`. -/
noncomputable def Phi (x : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi) * ∫ t in Set.Iic x, Real.exp (-(t ^ 2) / 2)

/-- The partial sum `S_n = x₁ + ⋯ + x_n`; the paper's `x_i` is `X (i - 1)`, so
`S n ω = X 0 ω + ⋯ + X (n - 1) ω` and `S 0 = 0`. -/
noncomputable def S {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The function `g(n₁, n₂, α)` of (24): the probability that `S_n > α n^{1/2}` for some `n`
with `n₁ ≤ n ≤ n₂` (both endpoints included). -/
noncomputable def g {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (n₁ n₂ : ℕ) (α : ℝ) : ℝ :=
  P.real {ω | ∃ n : ℕ, n₁ ≤ n ∧ n ≤ n₂ ∧ α * Real.sqrt n < S X n ω}

end RobbinsSeqDesign.OptionalStopping


