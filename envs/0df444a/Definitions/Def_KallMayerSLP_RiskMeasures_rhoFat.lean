-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_rhoFat
-- name    : KallMayerSLP_RiskMeasures_rhoFat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:07.778554+00:00
-- url     : https://prove2.me/theorems/2d494094-7ea8-4566-af27-83c7e096f30e
-- title:
--   Worst-case (fat solution) risk measure $\rho_{\mathrm{fat}}$
-- statement:
--   For an essentially bounded real random variable $\vartheta\in\mathcal L^\infty_1$ with support $\Theta$ (the support of its distribution),
--   $$
--   \rho_{\mathrm{fat}}(\vartheta):=\max_{\hat\vartheta\in\Theta}\hat\vartheta .
--   $$
--   This is the largest value that $\vartheta$ takes with positive probability in every neighbourhood: the worst possible loss. (The book changes the minimum of the fat-solution quality measure (1.17) to a maximum to obtain a risk measure.)
--
--   **Formalization Note** $\Theta$ is the topological support of the image measure $P\circ\vartheta^{-1}$, and the maximum is written as the supremum `sSup`. For $\vartheta\in\mathcal L^\infty_1$ on a probability space $\Theta$ is nonempty, closed and bounded, so the supremum is attained; it equals the essential supremum of $\vartheta$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.2, Proposition 7.3 (B), p.184 (PDF 194); support Θ, p.181 (PDF 191); (1.17), p.81 (PDF 91)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Worst-case ("fat solution") risk measure `ρ_fat`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.2, Prop. 7.3 (B), p.184 (PDF 194), with §1, p.81 and the notation of p.181 (PDF 191): `ρ_fat(ϑ) := max_{ϑ̂ ∈ Θ} ϑ̂`, `ϑ ∈ 𝓛^∞₁`, where `Θ` is the support of `ϑ`.

**Formalization Note.** `Θ` is the topological support of the distribution of `ϑ` (`Measure.support` of the image measure `P.map ϑ`: the points all of whose neighbourhoods have positive probability). The book's `max` is written `sSup`: for `ϑ ∈ 𝓛^∞₁` on a probability space `Θ` is closed, bounded and nonempty, so the supremum is attained and equals the maximum (and the essential supremum of `ϑ`). Off `𝓛^∞` the value is irrelevant. -/
noncomputable def rhoFat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ϑ : Ω → ℝ) : ℝ :=
  sSup (P.map ϑ).support

end KallMayerSLP.RiskMeasures


