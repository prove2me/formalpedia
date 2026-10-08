-- Prove2me | Definitions.Def_AgrawalGoyalTS_NArmed_BetaBinomial
-- name    : AgrawalGoyalTS_NArmed_BetaBinomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:10.78332+00:00
-- url     : https://prove2.me/theorems/f5d7355c-ce9f-4d93-a21b-ebebae02ab62
-- title:
--   Binomial pmf and cdf, i.i.d. Beta trials, and the trial count X(j, s, y)
-- statement:
--   This file fixes the distributional objects used in the analysis of Agrawal and Goyal.
--
--   1. **Binomial pmf and cdf.** For $n\in\mathbb N$, $p\in[0,1]$ and $k\in\mathbb N$, $f^B_{n,p}(k)=\binom nk p^k(1-p)^{n-k}$, and for a real $x$
--   $$F^B_{n,p}(x)=\Pr\big(\mathrm{Binomial}(n,p)\le x\big)=\sum_{0\le k\le n,\;k\le x} f^B_{n,p}(k).$$
--   2. **Independent Beta trials.** For natural numbers $a,b$, the law of an infinite sequence $W_0,W_1,\dots$ of independent $\mathrm{Beta}(a+1,b+1)$ random variables.
--   3. **The trial count $X(j,s,y)$** (p. 6). The experiment "is $W_n>y$?" is repeated until it succeeds, and $X$ is the number of trials *before* the first success:
--   $$X=\min\{n\ge 0: W_n>y\}\in\mathbb N\cup\{\infty\},$$
--   with $X=\infty$ when no trial succeeds. With $a=s$ and $b=j-s$ this is the paper's $X(j,s,y)$, a geometric random variable with success probability $1-F^{beta}_{s+1,j-s+1}(y)$.
--
--   These objects carry Lemma 1, Lemma 3 and Lemma 5 of the paper.
--
--   **Formalization Note** The law of the infinite i.i.d. sequence is Mathlib's `Measure.infinitePi`; an instance records that $\mathrm{Beta}(a+1,b+1)$ is a probability measure for natural $a,b$. The count is $\mathbb N_\infty$-valued, so a success probability $0$ (for instance $y=1$) gives $X=\infty$ rather than a junk value. This is a local copy of the same objects in the two-armed mission of this series.
-- source:
--   Agrawal and Goyal, Analysis of Thompson Sampling for the Multi-armed Bandit Problem, arXiv:1111.1797v3, p. 6 (definition of X(j, s, y) and F^B_{n,p})

import Mathlib
import Definitions.Def_AgrawalGoyalTS_TwoArmed_BetaBinomial

open MeasureTheory ProbabilityTheory

namespace AgrawalGoyalTS.NArmed

/-- `Beta(a+1, b+1)` is a probability measure for natural `a, b`. -/
instance instIsProbabilityMeasureBetaSucc (a b : ℕ) :
    IsProbabilityMeasure (betaMeasure ((a : ℝ) + 1) ((b : ℝ) + 1)) :=
  isProbabilityMeasureBeta (by positivity) (by positivity)

end AgrawalGoyalTS.NArmed


