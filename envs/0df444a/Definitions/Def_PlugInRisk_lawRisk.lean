-- Prove2me | Definitions.Def_PlugInRisk_lawRisk
-- name    : PlugInRisk_lawRisk
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:16.249921+00:00
-- url     : https://prove2.me/theorems/d769cbc3-e0b2-436c-bb8f-dec6beaf11af
-- title:
--   Risk of a law $\rho^\nu$
-- statement:
--   For a risk measure $\rho$ on the standard probability space $\Omega_0=[0,1]$ and a probability law $\nu$ on $\mathbb R$, the **risk of the law** is
--
--   $$
--   \rho(\nu):=\rho(Y)\qquad\text{for any random variable }Y\text{ on }\Omega_0\text{ with }Y\sim\nu .
--   $$
--
--   With $\mu$ the law of $S$ and $F$ a measurable function, the paper's shorthand is $\rho^\mu(F):=\rho(F(S))=\rho(\mu\circ F^{-1})$, and the plug-in estimator is $\rho^{\mu_N}(F)$ for the empirical measure $\mu_N$.
--
--   **Formalization Note** The value is the supremum of $\rho(Y)$ over all measurable $Y:[0,1]\to\mathbb R$ with law $\nu$. When $\nu$ has a finite $p$-th moment and $\rho$ is a risk measure on $L^p$, all such $Y$ lie in $L^p$ and have the same risk by law invariance, so the supremum is that common value. Every law on $\mathbb R$ is realized on $[0,1]$ by its quantile function.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, p.2 (ρ^µ(F) := ρ(F(S))) and Definition 1.3, p.3

import Mathlib

open MeasureTheory

namespace PlugInRisk

/-- **Risk of a law** `ρ^ν` (Bartl & Tangpi, arXiv:2003.10479v2, p.2: "ρ^μ(F) := ρ(F(S)) where
S ∼ μ"; Definition 1.3, p.3: "ρ^{μ_N}(F) = ρ(F(Ŝ)) where Ŝ ∼ μ_N").

For a law `ν` on `ℝ`, `lawRisk ρ ν` is `ρ(Y)` for any random variable `Y` on the standard
probability space with law `ν`. Then `ρ^μ(F) = lawRisk ρ (μ.map F)`.

**Formalization Note** The value is the supremum of `ρ Y` over all measurable `Y : [0,1] → ℝ`
with `volume.map Y = ν`. For a risk measure on `Lᵖ` (law invariance (d)) and a law `ν` with a
finite `p`-th moment, every such `Y` lies in `Lᵖ` and all of them give the same value, so the set
is a singleton and `lawRisk ρ ν = ρ(Y)`. Every law on `ℝ` is the law of a measurable function on
`[0,1]` (its quantile function). For a law outside `Lᵖ` the value is meaningless; every statement
of this mission applies `lawRisk` only to laws in `Lᵖ`. -/
noncomputable def lawRisk (ρ : (unitInterval → ℝ) → ℝ) (ν : Measure ℝ) : ℝ :=
  sSup {r : ℝ | ∃ Y : unitInterval → ℝ, Measurable Y ∧ volume.map Y = ν ∧ ρ Y = r}

end PlugInRisk


