-- Prove2me | Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial
-- name    : AgrawalGoyalTS_TwoArmed_BetaBinomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:25.310123+00:00
-- url     : https://prove2.me/theorems/86764c86-a100-4831-9115-250b5cb0db93
-- title:
--   Binomial and Beta cdfs, binomial medians, and the trial count X(j, s, y)
-- statement:
--   This file fixes the distributional objects used in the analysis of Agrawal and Goyal.
--
--   1. **Binomial pmf and cdf.** For $n\in\mathbb N$, $p\in[0,1]$ and $k\in\mathbb N$, $f^B_{n,p}(k)=\binom nk p^k(1-p)^{n-k}$, and for a real $x$
--   $$F^B_{n,p}(x)=\Pr\big(\mathrm{Binomial}(n,p)\le x\big)=\sum_{0\le k\le n,\;k\le x} f^B_{n,p}(k).$$
--   The upper tail $\Pr(\mathrm{Binomial}(n,p)\ge x)$ is the sum over $0\le k\le n$ with $k\ge x$.
--   2. **Median.** An integer $m$ is a median of $\mathrm{Binomial}(n,p)$ if $\Pr(X\le m)\ge 1/2$ and $\Pr(X\ge m)\ge 1/2$.
--   3. **Beta cdf.** $F^{beta}_{\alpha,\beta}(y)=\Pr(\mathrm{Beta}(\alpha,\beta)\le y)$, computed from Mathlib's beta measure (density $\frac{\Gamma(\alpha+\beta)}{\Gamma(\alpha)\Gamma(\beta)}x^{\alpha-1}(1-x)^{\beta-1}$ on $(0,1)$).
--   4. **The trial count $X(j,s,y)$.** Let $W_0,W_1,\dots$ be i.i.d. $\mathrm{Beta}(a+1,b+1)$ random variables. The experiment "is $W_n>y$?" is repeated until it succeeds, and the count is the number of trials *before* the first success:
--   $$X=\min\{n\ge 0: W_n>y\}\in\mathbb N\cup\{\infty\},$$
--   with $X=\infty$ when no trial succeeds. With $a=s$, $b=j-s$ this is the paper's $X(j,s,y)$, a geometric random variable with success probability $1-F^{beta}_{s+1,j-s+1}(y)$.
--
--   These objects carry Fact 1, Lemma 1, Fact 2, Lemma 6 and Lemma 3 of the paper.
--
--   **Formalization Note** The law of the infinite i.i.d. sequence is Mathlib's `Measure.infinitePi`; an instance records that $\mathrm{Beta}(a+1,b+1)$ is a probability measure for natural $a,b$. The count is $\mathbb N_\infty$-valued, so the degenerate case of a success probability $0$ (for instance $y=1$) gives $X=\infty$ rather than a junk value.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 6 (definition of X(j, s, y), F^beta, F^B), p. 13 (median of an integer-valued random variable)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace AgrawalGoyalTS.TwoArmed

/-- Binomial probability mass function `f^B_{n,p}(k) = C(n,k) p^k (1-p)^(n-k)`
(meaningful for `p ∈ [0,1]` and `k ≤ n`). -/
noncomputable def binomPMF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- Binomial cdf at a real point: `F^B_{n,p}(x) = Pr(Binomial(n,p) ≤ x)`. -/
noncomputable def binomCDF (n : ℕ) (p : ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => (k : ℝ) ≤ x), binomPMF n p k

/-- Upper binomial tail at a real point: `Pr(Binomial(n,p) ≥ x)`. -/
noncomputable def binomUpper (n : ℕ) (p : ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k : ℕ => x ≤ (k : ℝ)), binomPMF n p k

/-- An integer `m` is a median of `Binomial(n,p)` if `Pr(X ≤ m) ≥ 1/2` and `Pr(X ≥ m) ≥ 1/2`
(Agrawal–Goyal, App. B, p. 13). -/
def IsBinomialMedian (n : ℕ) (p : ℝ) (m : ℤ) : Prop :=
  1 / 2 ≤ binomCDF n p (m : ℝ) ∧ 1 / 2 ≤ binomUpper n p (m : ℝ)

/-- Beta cdf `F^beta_{α,β}(y) = Pr(Beta(α,β) ≤ y)` (Mathlib's `betaMeasure`). -/
noncomputable def betaCDF (α β y : ℝ) : ℝ :=
  (betaMeasure α β (Set.Iic y)).toReal

/-- `Beta(a+1, b+1)` is a probability measure for natural `a, b`. -/
instance instIsProbabilityMeasureBetaSucc (a b : ℕ) :
    IsProbabilityMeasure (betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1)) :=
  isProbabilityMeasureBeta (by positivity) (by positivity)

/-- The law of an infinite i.i.d. sequence `W_0, W_1, …` of `Beta(a+1, b+1)` random variables. -/
noncomputable def betaTrials (a b : ℕ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1))

/-- The number of trials before the first success of the experiment "the trial value exceeds
`y`": the least `n` with `y < ω n`, and `⊤` if no trial ever succeeds. With
`ω ∼ betaTrials s (j - s)` this is the paper's `X(j, s, y)` (p. 6). -/
noncomputable def firstExceed (y : ℝ) (ω : ℕ → ℝ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : y < ω n), (n : ℕ∞)

end AgrawalGoyalTS.TwoArmed


