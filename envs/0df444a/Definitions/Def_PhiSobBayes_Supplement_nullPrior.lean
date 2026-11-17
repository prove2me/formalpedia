-- Prove2me | Definitions.Def_PhiSobBayes_Supplement_nullPrior
-- name    : PhiSobBayes_Supplement_nullPrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:44:33.014204+00:00
-- url     : https://prove2.me/theorems/38b77049-2268-4a8e-93d9-88229999ed7b
-- title:
--   Null-posterior prior $\nu_t = \int \mu_{t,y}\,\gamma_n(dy)$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$ and $t>0$. For $y\in\mathbb R^n$ let $\mu_{t,y}$ be the posterior of the Gaussian additive model at SNR $t$ (Bayes' formula (44)),
--
--   $$
--   \mu_{t,y}(\mathrm dx)=\frac{e^{-\|y-\sqrt t\,x\|^2/2}\,\mu(\mathrm dx)}{\int e^{-\|y-\sqrt t\,x'\|^2/2}\,\mu(\mathrm dx')}.
--   $$
--
--   The **null-posterior prior** is the average of these posteriors over a pure-noise observation $y\sim\gamma_n=N(0,I_n)$:
--
--   $$
--   \nu_t=\int_{\mathbb R^n}\mu_{t,y}\,\gamma_n(\mathrm dy),\qquad\text{i.e.}\qquad \nu_t(A)=\int\mu_{t,y}(A)\,\gamma_n(\mathrm dy)\ \text{ for every measurable }A .
--   $$
--
--   It is the prior of the paper's null-posterior model and the reference measure in the divergence $\chi^2(\mu\,\|\,\nu_t)$ of Theorem 4.9.
--
--   **Formalization Note** $\nu_t$ is defined as $\mu$ with density $x\mapsto\int e^{-\|y-\sqrt t\,x\|^2/2}/Z_t(y)\,\gamma_n(\mathrm dy)$, where $Z_t(y)$ is the normaliser above; by Tonelli's theorem this agrees with the mixture on every measurable set, without any measurability side condition (proved in the mission's verification file).
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), display (6), p.11 (PDF 11); p.18 (PDF 18); display (44), p.29 (PDF 29)

import Mathlib
import Definitions.Def_PhiSobBayes_posterior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PhiSobBayes.Supplement

/-- The **null-posterior prior** `ν_t = ∫_{ℝⁿ} μ_{t,y} γ_n(dy) = 𝔼_{y∼γ_n} μ_{t,y}`: the average of the
posteriors `μ_{t,y}` (Bayes' formula (44)) over a pure-noise observation `y ∼ γ_n = N(0, I_n)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027
submission (held version, sha256 5ea05e95…8ed487), display (6), p.11 (PDF 11): "𝜈𝑡 := ∫_{ℝ𝑛} 𝜇𝑡,𝑦 𝛾𝑛(d𝑦)";
recalled on p.18 (PDF 18) as "𝜈𝑡 = 𝔼_{𝑦∼𝛾𝑛} 𝜇𝑡,𝑦"; the posterior is display (44), p.29 (PDF 29).

**Formalization Note** Defined as `μ` with density
`x ↦ ∫⁻ ofReal(e^{−‖y − √t x‖²/2} / Z_t(y)) γ_n(dy)`, `Z_t(y) = ∫ e^{−‖y − √t x′‖²/2} μ(dx′)`,
which is the density of the published `PhiSobBayes.posterior μ t y` averaged over `y`. By Tonelli,
`ν_t(A) = ∫⁻ posterior μ t y A ∂γ_n(y)` for **every** measurable `A`, with no measurability side
condition (proved for every finite `μ` in the verification file). `γ_n` is Mathlib's `stdGaussian`. -/
noncomputable def nullPrior {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  μ.withDensity (fun x => ∫⁻ y, ENNReal.ofReal (Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) /
      ∫ x', Real.exp (-‖y - Real.sqrt t • x'‖ ^ 2 / 2) ∂μ) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))))

end PhiSobBayes.Supplement


