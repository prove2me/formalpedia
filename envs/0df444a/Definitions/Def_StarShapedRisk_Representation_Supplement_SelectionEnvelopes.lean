-- Prove2me | Definitions.Def_StarShapedRisk_Representation_Supplement_SelectionEnvelopes
-- name    : StarShapedRisk_Representation_Supplement_SelectionEnvelopes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:39:52.979266+00:00
-- url     : https://prove2.me/theorems/facda399-3297-44ca-9baf-c497d52c9c28
-- title:
--   Relaxation and the selection families of Theorem 3
-- statement:
--   For a linear space $\mathcal X$ of bounded losses and a set $\Gamma$ of risk functionals, define
--   $$\widetilde\Gamma=\{\delta:\delta\text{ is a convex risk measure and }\forall X\in\mathcal X\ \exists\gamma\in\Gamma,\ \gamma(X)\le\delta(X)\}.$$
--   For a family $\Gamma_i$, its average-selection family consists of all $X\mapsto\int\gamma_i(X)\,d\mu(i)$ with $\gamma_i\in\Gamma_i$ for every $i$. For a finite family its inf-convolution-selection family consists of all $\square_i\gamma_i$ with the same selection condition. These families are the optimization domains in (13), (14), and (16).
--
--   **Formalization Note** Theorems impose the source's probability and normality conditions; these total definitions alone do not assert integrability or finiteness.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2644, def-relaxation

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure
import Definitions.Def_StarShapedRisk_Representation_Aggregation

namespace StarShapedRisk.Representation.Supplement

/-- The relaxation before Proposition 4; the choice may depend on the position. -/
def relaxation {Ω : Type*} (𝒳 : PositionSpace Ω)
    (Γ : Set (𝒳.carrier → ℝ)) : Set (𝒳.carrier → ℝ) :=
  {δ | IsConvexRiskMeasure 𝒳 δ ∧ ∀ X, ∃ γ ∈ Γ, γ X ≤ δ X}

/-- All averages of selections in (13), without a measurability restriction on selections. -/
noncomputable def averageSelections {Ω I : Type*} (𝒳 : PositionSpace Ω)
    [MeasurableSpace I] (μ : MeasureTheory.Measure I)
    (Γ : I → Set (𝒳.carrier → ℝ)) : Set (𝒳.carrier → ℝ) :=
  {δ | ∃ γ : I → 𝒳.carrier → ℝ, (∀ i, γ i ∈ Γ i) ∧ δ = riskAverage 𝒳 μ γ}

/-- All inf-convolutions of selections in (16). -/
noncomputable def infConvolutionSelections {Ω : Type*} (𝒳 : PositionSpace Ω) {n : ℕ}
    (Γ : Fin n → Set (𝒳.carrier → ℝ)) : Set (𝒳.carrier → ℝ) :=
  {δ | ∃ γ : Fin n → 𝒳.carrier → ℝ, (∀ i, γ i ∈ Γ i) ∧ δ = infConvolution 𝒳 γ}

end StarShapedRisk.Representation.Supplement


