-- Prove2me | Definitions.Def_PrivBayesTest_chernoff
-- name    : PrivBayesTest_chernoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:52.502107+00:00
-- url     : https://prove2.me/theorems/be9984a6-1b92-4a64-bcf2-5d2bd4cead92
-- title:
--   Chernoff information $C(\mu;\nu)=\sup_{\alpha\in(0,1)}-\log\int d\mu^\alpha d\nu^{1-\alpha}$
-- statement:
--   Let $\mu,\nu$ be measures on a measurable space $\mathcal X$ and let $\rho=\mu+\nu$, with densities $p=d\mu/d\rho$ and $q=d\nu/d\rho$. For $\alpha\in\mathbb R$ the **Hellinger affinity** is
--
--   $$
--   \int d\mu^\alpha\, d\nu^{1-\alpha} \;=\; \int p^\alpha q^{1-\alpha}\, d\rho \in [0,\infty],
--   $$
--
--   and the **Chernoff information** of $\mu$ and $\nu$ is
--
--   $$
--   C(\mu;\nu) \;=\; \sup_{\alpha\in(0,1)} \Big(-\log \int d\mu^\alpha\, d\nu^{1-\alpha}\Big).
--   $$
--
--   This is eq. (1) of the paper: for probability measures it is the optimal exponent of the Bayes risk of (non-private) testing between $\mu^n$ and $\nu^n$.
--
--   **Formalization Note** The affinity is a lower integral, so it needs no integrability hypothesis and does not depend on the dominating measure. Values of $C$ are extended reals with $-\log 0=+\infty$; for probability measures $C(\mu;\nu)\in[0,+\infty]$, and $C(\mu;\nu)=+\infty$ exactly when $\mu\perp\nu$.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), eq. (1), p.1

import Mathlib

open MeasureTheory

namespace PrivBayesTest

/-- The **Hellinger affinity** `∫ dμ^α dν^{1−α}` of two measures, the integrand of eq. (1) of
Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), eq. (1), p.1.

**Formalization Note** The integral is taken against the dominating measure `ρ = μ + ν` with the
Radon–Nikodym densities `dμ/dρ`, `dν/dρ`; its value does not depend on the dominating measure.
It is a lower (extended nonnegative) integral, so no integrability hypothesis is needed and the
value `0` (mutually singular measures) is allowed. -/
noncomputable def affinity {X : Type*} [MeasurableSpace X] (α : ℝ) (μ ν : Measure X) : ENNReal :=
  ∫⁻ x, (μ.rnDeriv (μ + ν) x) ^ α * (ν.rnDeriv (μ + ν) x) ^ (1 - α) ∂(μ + ν)

/-- The **Chernoff information** of Jacobsen, *Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), eq. (1), p.1:
`C(μ; ν) = sup_{α ∈ (0,1)} −log ∫ dμ^α dν^{1−α}`.

**Formalization Note** Values are in `EReal`: the supremum is the extended-real supremum over
`α ∈ (0,1)`, and `−log 0 = +∞`, so `C(μ; ν) = ⊤` when `μ` and `ν` are mutually singular. For
probability measures the affinity lies in `[0,1]` and `C(μ; ν) ∈ [0, ⊤]`. No absolute continuity or
finiteness hypothesis is imposed. -/
noncomputable def chernoff {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : EReal :=
  ⨆ α ∈ Set.Ioo (0 : ℝ) 1, -ENNReal.log (affinity α μ ν)

end PrivBayesTest


