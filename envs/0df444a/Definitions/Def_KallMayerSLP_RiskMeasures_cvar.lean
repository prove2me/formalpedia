-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_cvar
-- name    : KallMayerSLP_RiskMeasures_cvar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:09.854339+00:00
-- url     : https://prove2.me/theorems/2adb1715-7768-4432-8d24-bcbe177c0544
-- title:
--   Conditional value-at-risk $\rho^\alpha_{\mathrm{CVaR}}=\nu_c(\cdot,\alpha)$
-- statement:
--   For a real random variable $\vartheta\in\mathcal L^1_1$ and a level $0<\alpha<1$,
--   $$
--   \rho^\alpha_{\mathrm{CVaR}}(\vartheta):=\nu_c(\vartheta,\alpha):=\min_{z\in\mathbb R}\Big[z+\frac1{1-\alpha}\,\mathbb E\big[(\vartheta-z)^+\big]\Big],
--   $$
--   where $t^+=\max\{0,t\}$. This is the Rockafellar–Uryasev minimization formula for the conditional value-at-risk of the loss $\vartheta$.
--
--   **Formalization Note** The minimum is written as the real infimum over $z$. For $\vartheta\in\mathcal L^1_1$ and $0<\alpha<1$ the objective is bounded below by $\mathbb E[\vartheta]$, so the infimum is finite; that it is attained is a theorem of §4.3, not part of the definition.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.3 (C), p.184 (PDF 194), with §4.3

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Conditional value-at-risk `ρ^α_CVaR = ν_c(·, α)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.3 (C), p.184 (PDF 194), with §4.3: `ρ^α_CVaR(ϑ) := ν_c(ϑ, α) := min_z [ z + (1/(1 − α)) 𝔼[(ϑ − z)⁺] ]`, `ϑ ∈ 𝓛¹₁`, `0 < α < 1`.

**Formalization Note.** The book's `min` is the real infimum `⨅ z`; that it is attained (for `ϑ ∈ 𝓛¹₁`, `0 < α < 1`) is a theorem of §4.3, not part of the definition. For such `ϑ, α` the objective is bounded below by `𝔼[ϑ]`, so the infimum is a genuine one. `z⁺ = max{0, z}`. -/
noncomputable def cvar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℝ) (ϑ : Ω → ℝ) : ℝ :=
  ⨅ z : ℝ, (z + (1 / (1 - α)) * ∫ ω, max (ϑ ω - z) 0 ∂P)

end KallMayerSLP.RiskMeasures


