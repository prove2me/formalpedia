-- Prove2me | Definitions.Def_StarShapedRisk_Representation_Aggregation
-- name    : StarShapedRisk_Representation_Aggregation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:47:56.568684+00:00
-- url     : https://prove2.me/theorems/02eef462-fb09-459e-b403-a3bfe8b0ba46
-- title:
--   Aggregation of risk measures: average, supremum, infimum, inf-convolution
-- statement:
--   Let $\{\rho_i\}_{i\in I}$ be a collection of functions $\mathcal X\to\mathbb R$ on a space of positions $\mathcal X$.
--
--   1. For a probability $\mu$ on the subsets of $I$, the **average** is $\rho_\mu(X)=\int_I\rho_i(X)\,d\mu(i)$ (Eq. (8)).
--   2. The **supremum** is $\rho_\vee(X)=\sup_{i\in I}\rho_i(X)$.
--   3. The **infimum** is $\rho_\wedge(X)=\inf_{i\in I}\rho_i(X)$.
--   4. For $I=\{1,\dots,n\}$ finite, the **inf-convolution** is
--   $$\rho_\diamond(X)=\inf\Big\{\sum_{i\in I}\rho_i(Y_i)\ \Big|\ Y_i\in\mathcal X\text{ for all }i,\ \sum_{i\in I}Y_i=X\Big\}\qquad(9)$$
--   and it is considered under the **normality condition** $\sum_{i\in I}\rho_i(Z_i)\ge 0$ for all $Z_1,\dots,Z_n\in\mathcal X$ with $\sum_i Z_i=0$ (Eq. (10)).
--
--   These operations model the aggregation of several risk assessments into one; Theorem 1 of the paper shows that star-shaped risk measures are closed under all four.
--
--   **Formalization Note** The average is a Bochner integral over a measure on $I$; the supremum and infimum are `⨆`/`⨅` in $\mathbb R$ and the inf-convolution a real `sInf`. These return junk values ($0$) for non-integrable, empty or unbounded families, so the theorems using them add the page's implicit hypotheses: the power-set σ-algebra and a probability measure for the average, a nonempty index set for sup and inf, and $n>0$ with condition (10) for the inf-convolution. Under those hypotheses and for risk measures $\rho_i$, the values are the genuine ones.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), p. 2643, Section 4, Eqs. (8), (9), (10)

import Mathlib
import Definitions.Def_StarShapedRisk_Representation_RiskMeasure

namespace StarShapedRisk.Representation

variable {Ω : Type*}

/-- The average `ρ_μ X = ∫_I ρ_i X dμ(i)` of a family `{ρ_i}` (Eq. (8), p. 2643), a Bochner
integral with respect to a measure `μ` on the index set `I`. -/
noncomputable def riskAverage (𝒳 : PositionSpace Ω) {I : Type*} [MeasurableSpace I]
    (μ : MeasureTheory.Measure I) (ρ : I → 𝒳.carrier → ℝ) (X : 𝒳.carrier) : ℝ :=
  ∫ i, ρ i X ∂μ

/-- The supremum `ρ_∨ X = sup_{i ∈ I} ρ_i X` (p. 2643). -/
noncomputable def riskSup (𝒳 : PositionSpace Ω) {I : Type*} (ρ : I → 𝒳.carrier → ℝ)
    (X : 𝒳.carrier) : ℝ :=
  ⨆ i, ρ i X

/-- The infimum `ρ_∧ X = inf_{i ∈ I} ρ_i X` (p. 2643). -/
noncomputable def riskInf (𝒳 : PositionSpace Ω) {I : Type*} (ρ : I → 𝒳.carrier → ℝ)
    (X : 𝒳.carrier) : ℝ :=
  ⨅ i, ρ i X

/-- The inf-convolution of `ρ_1, …, ρ_n` (Eq. (9), p. 2643):
`ρ_◇ X = inf {∑ ρ_i (Y_i) | Y_i ∈ 𝒳, ∑ Y_i = X}`. -/
noncomputable def infConvolution (𝒳 : PositionSpace Ω) {n : ℕ} (ρ : Fin n → 𝒳.carrier → ℝ)
    (X : 𝒳.carrier) : ℝ :=
  sInf {s : ℝ | ∃ Y : Fin n → 𝒳.carrier, ∑ i, Y i = X ∧ s = ∑ i, ρ i (Y i)}

/-- Condition (10): `∑ ρ_i (Z_i) ≥ 0` whenever `∑ Z_i = 0`. -/
def NormalityCondition (𝒳 : PositionSpace Ω) {n : ℕ} (ρ : Fin n → 𝒳.carrier → ℝ) : Prop :=
  ∀ Z : Fin n → 𝒳.carrier, ∑ i, Z i = 0 → 0 ≤ ∑ i, ρ i (Z i)

end StarShapedRisk.Representation


