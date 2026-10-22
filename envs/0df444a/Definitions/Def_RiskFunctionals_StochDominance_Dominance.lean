-- Prove2me | Definitions.Def_RiskFunctionals_StochDominance_Dominance
-- name    : RiskFunctionals_StochDominance_Dominance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:56.443502+00:00
-- url     : https://prove2.me/theorems/475c757c-536c-45a6-9abd-3163a9cdf9e9
-- title:
--   Stochastic dominance of first and second order, concave and convex dominance, defined through utility classes
-- statement:
--   Let $G_1$ and $G_2$ be distribution functions on $\mathbb R$ (laws $\mu_1$, $\mu_2$). Following Definition 1.10, four order relations are defined through classes of utility functions $U:\mathbb R\to\mathbb R$; in each case the comparison is required for every $U$ of the class **for which the integrals exist**.
--
--   1. **First-order stochastic dominance** $G_1 \prec_{FSD} G_2$: for every nondecreasing $U$ that is integrable with respect to both $G_1$ and $G_2$,
--   $$\int U(v)\,dG_1(v) \le \int U(v)\,dG_2(v).$$
--   2. **Second-order stochastic dominance** $G_1 \prec_{SSD} G_2$: the same inequality for every nondecreasing concave $U$ integrable with respect to both.
--   3. **Concave dominance** $G_1 \prec_{CCD} G_2$: the same inequality for every concave $U$ integrable with respect to both.
--   4. **Convex dominance** $G_1 \prec_{CXD} G_2$: the same inequality for every convex $U$ integrable with respect to both.
--
--   The book works with profit variables (larger is better), so $G_1 \prec G_2$ means that $G_2$ is preferred by every decision maker whose utility lies in the class. For random variables $Y^{(1)}, Y^{(2)}$ the same relations are written $Y^{(1)} \prec Y^{(2)}$ and refer to their laws.
--
--   **Formalization Note** Distributions are probability measures on $\mathbb R$ (they may be laws of random variables on different probability spaces). "For which the integrals exist" is encoded as `Integrable U μ₁` and `Integrable U μ₂`, i.e. $\int |U|\,dG_i < \infty$ for both $i$: a universal quantifier over all utilities of the class, without this side condition, would compare junk values. Concavity and convexity are on the whole real line (`ConcaveOn ℝ Set.univ`, `ConvexOn ℝ Set.univ`); "nondecreasing" is `Monotone`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 12–14, §1.2.3, Definition 1.10

import Mathlib

namespace RiskFunctionals.StochDominance

open MeasureTheory

/-- First-order stochastic dominance `G₁ ≺_FSD G₂` (Pflug & Römisch, p. 13, Definition 1.10(i)),
for distributions given as probability measures `μ₁`, `μ₂` on `ℝ`:
`∫ U dG₁ ≤ ∫ U dG₂` for every nondecreasing `U` for which both integrals exist. -/
def FSD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- Second-order stochastic dominance `G₁ ≺_SSD G₂` (p. 13, Definition 1.10(ii)):
`∫ U dG₁ ≤ ∫ U dG₂` for every nondecreasing concave `U` for which both integrals exist. -/
def SSD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, Monotone U → ConcaveOn ℝ Set.univ U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- Concave dominance `G₁ ≺_CCD G₂` (p. 13, Definition 1.10(iii)):
`∫ U dG₁ ≤ ∫ U dG₂` for every concave `U` for which both integrals exist. -/
def CCD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, ConcaveOn ℝ Set.univ U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- Convex dominance `G₁ ≺_CXD G₂` (p. 14, Definition 1.10(iv)):
`∫ U dG₁ ≤ ∫ U dG₂` for every convex `U` for which both integrals exist. -/
def CXD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, ConvexOn ℝ Set.univ U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

end RiskFunctionals.StochDominance


