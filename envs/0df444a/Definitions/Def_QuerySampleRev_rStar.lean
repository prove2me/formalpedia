-- Prove2me | Definitions.Def_QuerySampleRev_rStar
-- name    : QuerySampleRev_rStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:50.362823+00:00
-- url     : https://prove2.me/theorems/36c9cced-bbb1-4420-bdd1-4a0486f2cf91
-- title:
--   Sale probability $Q(p)$, left-continuous CDF $F(p)$, revenue $R_{\mathrm{pr}}(p)$ and optimal revenue $r^*$
-- statement:
--   Let $F$ be a value distribution, encoded as a measure $\mu$ on $\mathbb R$. With the paper's sale convention (a buyer whose value equals the posted price buys),
--   $$
--   F(p)=\mathbb P_{v\sim F}[v<p],\qquad Q(p)=1-F(p)=\mathbb P_{v\sim F}[v\ge p].
--   $$
--   The **revenue-price curve** and the **optimal revenue** are
--   $$
--   R_{\mathrm{pr}}(p)=p\,Q(p),\qquad r^*=\sup_{p\ge 0}R_{\mathrm{pr}}(p).
--   $$
--   These are the basic objects of single-buyer revenue maximization: a posted price $p$ earns $p$ exactly when the value is at least $p$.
--
--   **Formalization Note** $Q(p)=\mu([p,\infty))$ and $F(p)=\mu((-\infty,p))$ are in $[0,\infty]$; revenue is $\mathrm{ofReal}(p)\cdot Q(p)$ in $[0,\infty]$ (so a negative price earns $0$), and $r^*$ is the supremum in $[0,\infty]$ over $p\ge0$, equal to $+\infty$ for an unbounded revenue curve.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF p.13), display defining F and Q; §2.2, p.13 (PDF p.15), display defining R_pr and r∗

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Sale probability `Q(p)`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF 13):
"`F(p) ≜ P_{v∼F}[v < p]`, `Q(p) ≜ 1 − F(p) = P_{v∼F}[v ≥ p]`, `p ≥ 0`."

For a value law `μ` on `ℝ`, `saleProb μ p = μ([p, ∞)) = P_{v∼μ}[v ≥ p]`: a buyer whose value equals the
posted price buys.

**Formalization Note.** A value distribution is a measure `μ : Measure ℝ`; the paper's standing
assumptions (probability measure, supported on `[0, ∞)`) are stated where they are used. -/
noncomputable def saleProb (μ : Measure ℝ) (p : ℝ) : ℝ≥0∞ := μ (Set.Ici p)

/-- **Left-continuous CDF `F(p)`.** Same source, §2.1, p.11 (PDF 13): "We use the same notation `F` for
a distribution and its left-continuous cumulative distribution function (CDF)", `F(p) ≜ P_{v∼F}[v < p]`.
Here `cdf μ p = μ((−∞, p))`. -/
noncomputable def cdf (μ : Measure ℝ) (p : ℝ) : ℝ≥0∞ := μ (Set.Iio p)

/-- **Revenue-price curve `R_pr(p) = p Q(p)`.** Same source, §2.2, p.13 (PDF 15):
"`R_pr(p) ≜ pQ(p) = p(1 − F(p))`".

**Formalization Note.** Valued in `ℝ≥0∞`; the price enters as `ENNReal.ofReal p`, so a negative price
earns revenue `0` (the paper only uses prices `p ≥ 0`). -/
noncomputable def revenue (μ : Measure ℝ) (p : ℝ) : ℝ≥0∞ := ENNReal.ofReal p * saleProb μ p

/-- **Optimal revenue `r∗`.** Same source, §2.2, p.13 (PDF 15): "`r∗ ≜ sup_{p≥0} R_pr(p)`. We consider
distributions with finite optimal revenue."

**Formalization Note.** The supremum is taken in `ℝ≥0∞` over prices `p ≥ 0`, so it is `⊤` when the revenue
curve is unbounded (no junk value); finiteness of `r∗` is a separate clause of the distribution family
(`InFamily`). -/
noncomputable def rStar (μ : Measure ℝ) : ℝ≥0∞ := ⨆ (p : ℝ) (_ : 0 ≤ p), revenue μ p

end QuerySampleRev


