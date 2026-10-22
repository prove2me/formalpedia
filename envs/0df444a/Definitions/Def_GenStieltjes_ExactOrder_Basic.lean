-- Prove2me | Definitions.Def_GenStieltjes_ExactOrder_Basic
-- name    : GenStieltjes_ExactOrder_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:20.153466+00:00
-- url     : https://prove2.me/theorems/1eafc5fd-9fe9-4984-a20d-9fff86531727
-- title:
--   (2), (10), (24), (25), Definition A1 — M_α, left-continuous F_μ, I^+_η μ, the measure μ_β of Theorem 3, exact Stieltjes order, Φ
-- statement:
--   Throughout, a **measure on $[0,\infty)$** is a Borel measure $\mu$ on $\mathbb R_{\ge 0}$; a possible atom at $0$ is part of $\mu$. For $\alpha>0$, the generalized Stieltjes class $S_\alpha$ is the class of functions $f$ on $(0,\infty)$ of the form
--   $$f(z)=\mu_\infty+\int_{[0,\infty)}\frac{\mu(dt)}{(z+t)^\alpha},\qquad \mu_\infty\ge 0,$$
--   with $\mu$ satisfying condition (2) below (this is the published definition `StieltjesClass` that the mission imports). This file defines the further objects of the paper.
--
--   1. **Condition (2), the cone $\mathcal M_\alpha$.** $\mu\in\mathcal M_\alpha$ means
--   $$\int_{[0,\infty)}\frac{\mu(dt)}{(1+t)^\alpha}<\infty .$$
--   2. **Left-continuous distribution function.** $F_\mu(y)=\mu([0,y))$ for $y\ge 0$, so that $F_\mu(0)=0$; its values lie in $[0,\infty]$.
--   3. **Riemann–Liouville fractional integral of a measure (Definition A1).** For $\eta>0$, $I^+_\eta\mu$ is the measure on $[0,\infty)$ that is absolutely continuous with respect to Lebesgue measure on $(0,\infty)$, with density
--   $$y\longmapsto \frac{1}{\Gamma(\eta)}\int_{[0,y)}\frac{\mu(du)}{(y-u)^{1-\eta}} .$$
--   4. **The measure of Theorem 3, formula (10).** For $\alpha<\beta$, $\mu_\beta$ is the measure on $[0,\infty)$ with Lebesgue density on $(0,\infty)$
--   $$y\longmapsto\frac{\Gamma(\beta)}{\Gamma(\alpha)\Gamma(\beta-\alpha)}\int_{[0,y)}\frac{\mu_\alpha(du)}{(y-u)^{\alpha+1-\beta}} .$$
--   5. **Exact Stieltjes order, formula (24).** For $f$ on $(0,\infty)$,
--   $$\alpha^*[f]=\inf\{\alpha>0:\ f\in S_\alpha\}.$$
--   6. **The function $\Phi$ of formula (25).** For a measure $\mu$ and $\varepsilon\in\mathbb R$,
--   $$\Phi(y)=\int_{[0,y)}\frac{\mu(du)}{(y-u)^{\varepsilon}},\qquad y\ge 0,$$
--   with values in $[0,\infty]$.
--
--   These are the objects in which the criterion of exactness (Theorem 16) and the results it uses (Theorem 3, Theorem A1) are stated.
--
--   **Formalization Note** Measures live on `ℝ≥0`; the paper's atom at $+\infty$ is not a measure on `ℝ≥0` and is carried, where it matters, by the constant $\mu_\infty$ of the representation. The densities in items 3 and 4 are taken against Lebesgue measure restricted to $(0,\infty)$ and pushed to `ℝ≥0` along `Real.toNNReal`, so the measures in items 3 and 4 have no atom at $0$ (Remark A1). All kernel integrals are lower Lebesgue integrals in $[0,\infty]$, so a divergent integral is $+\infty$, never a junk $0$. The infimum in item 5 is the real infimum of a set of positive reals; the theorems apply it only when the set is nonempty. Item 6 integrates over $[0,y)$; the paper prints $(0,y)$ in (25), a slip discussed in Theorem 16.
-- source:
--   Karp & Prilepkina, Generalized Stieltjes transforms: basic aspects, arXiv:1111.4271v2, pp. 2–4, 11, 15, (1)–(2), (10), (24)–(25), Definition A1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

namespace GenStieltjes.ExactOrder

open MeasureTheory
open scoped NNReal ENNReal
open QAlgorithms.Papers.Independent.Renew46.P11 (PositiveReal StieltjesRepresentation StieltjesClass)

/-- Condition (2), p. 2: `μ ∈ M_α` (restricted to `[0, ∞)`; the atom at `∞` is carried
separately as a constant): `∫_{[0,∞)} μ(dt) / (1 + t)^α < ∞`. -/
def InM (α : ℝ) (μ : Measure ℝ≥0) : Prop :=
  ∫⁻ t, ENNReal.ofReal ((1 + (t : ℝ)) ^ (-α)) ∂μ < ⊤

/-- The left-continuous distribution function `F_μ(y) = μ([0, y))`, normalized by
`F_μ(0) = 0` (p. 3). -/
def distFn (μ : Measure ℝ≥0) (y : ℝ≥0) : ℝ≥0∞ :=
  μ (Set.Iio y)

/-- The measure on `[0, ∞)` with density `g` with respect to Lebesgue measure on `(0, ∞)`
(it has no atom at `0`). -/
noncomputable def densityMeasure (g : ℝ → ℝ≥0∞) : Measure ℝ≥0 :=
  Measure.map Real.toNNReal ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity g)

/-- Definition A1, (27), p. 15, on `[0, ∞)`: the left-sided Riemann–Liouville fractional
integral `I^+_η μ`, the measure with density
`y ↦ (1/Γ(η)) ∫_{[0,y)} μ(du) / (y − u)^{1−η}` on `(0, ∞)`. -/
noncomputable def rlIntegral (η : ℝ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  densityMeasure fun y => ENNReal.ofReal (1 / Real.Gamma η) *
    ∫⁻ u in Set.Iio y.toNNReal, ENNReal.ofReal ((y - (u : ℝ)) ^ (-(1 - η))) ∂μ

/-- Formula (10), p. 4: the measure
`μ_β(dy) = Γ(β) dy / (Γ(α)Γ(β − α)) ∫_{[0,y)} μ_α(du) / (y − u)^{α+1−β}` on `(0, ∞)`. -/
noncomputable def thm3Measure (α β : ℝ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  densityMeasure fun y =>
    ENNReal.ofReal (Real.Gamma β / (Real.Gamma α * Real.Gamma (β - α))) *
      ∫⁻ u in Set.Iio y.toNNReal, ENNReal.ofReal ((y - (u : ℝ)) ^ (-(α + 1 - β))) ∂μ

/-- Formula (24), p. 11: the exact Stieltjes order `α*[f] = inf {α > 0 : f ∈ S_α}`. -/
noncomputable def exactOrder (f : PositiveReal → ℝ) : ℝ :=
  sInf {α : ℝ | 0 < α ∧ f ∈ StieltjesClass α}

/-- Formula (25), p. 11, with the integral over `[0, y)` (the paper prints `(0, y)`):
`Φ(y) = ∫_{[0,y)} μ(du) / (y − u)^ε`, valued in `[0, ∞]`. -/
noncomputable def Phi (μ : Measure ℝ≥0) (ε : ℝ) (y : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ u in Set.Iio y, ENNReal.ofReal (((y : ℝ) - (u : ℝ)) ^ (-ε)) ∂μ

end GenStieltjes.ExactOrder


