-- Prove2me | Definitions.Def_PlugInRisk_empiricalMeasure
-- name    : PlugInRisk_empiricalMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:52.770555+00:00
-- url     : https://prove2.me/theorems/35e041b2-8780-4453-b6ba-0d3239d712e2
-- title:
--   Empirical measure $\mu_N$
-- statement:
--   Given observations $S_1(\omega),\dots,S_N(\omega)$ in $\mathcal X$, the **empirical measure** is
--
--   $$
--   \mu_N:=\frac1N\sum_{n\le N}\delta_{S_n}.
--   $$
--
--   It is a random probability measure for $N\ge1$, and $\rho^{\mu_N}(F)$ is the plug-in estimator of $\rho^\mu(F)$.
--
--   **Formalization Note** It is the published empirical distribution `WassersteinDRO.ConvexLossP1.empirical` ($N^{-1}\sum_i\delta_{\xi_i}$) of the points $S_0(\omega),\dots,S_{N-1}(\omega)$; observations are indexed from $0$.
-- source:
--   Bartl & Tangpi, Non-asymptotic convergence rates for the plug-in estimation of risk measures, arXiv:2003.10479v2, p.3 and §2, p.6

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_empirical

open MeasureTheory

namespace PlugInRisk

/-- **Empirical measure** (Bartl & Tangpi, arXiv:2003.10479v2, p.3 and §2, p.6):
`μ_N := (1/N) Σ_{n≤N} δ_{S_n}`, built from the sample `S₁, …, S_N`.

`empiricalMeasure S N ω` is the empirical measure of the first `N` observations of the sequence
`S` at the sample point `ω`: the published empirical distribution
`WassersteinDRO.ConvexLossP1.empirical` (`N⁻¹ • ∑ᵢ δ_{ξᵢ}`) of the `N` points `S 0 ω, …,
S (N-1) ω`.

**Formalization Note** The sample is indexed from `0`: the observations are
`S 0 ω, …, S (N-1) ω`. For `N ≥ 1` this is a probability measure. -/
noncomputable def empiricalMeasure {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] (S : ℕ → Ω → 𝒳) (N : ℕ)
    (ω : Ω) : Measure 𝒳 :=
  WassersteinDRO.ConvexLossP1.empirical (fun i : Fin N => S i ω)

end PlugInRisk


