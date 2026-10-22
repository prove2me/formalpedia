-- Prove2me | Definitions.Def_RiskFunctionals_Distortion_Orders
-- name    : RiskFunctionals_Distortion_Orders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:52:16.284197+00:00
-- url     : https://prove2.me/theorems/bf857520-0e8b-4df0-8c1a-a72baa68c21b
-- title:
--   Uniform $[0,1]$ random variables, the convex order $\prec_{CXD}$ and comonotonicity
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space.
--
--   1. A random variable $U$ is **uniform on $[0,1]$** if it is measurable and its law is Lebesgue measure on $[0,1]$.
--   2. **Convex dominance**: a distribution $G_1$ is dominated by $G_2$ in the convex order, $G_1\prec_{CXD}G_2$, if
--   $$\int U(v)\,dG_1(v)\le\int U(v)\,dG_2(v)$$
--   for every convex $U$ for which both integrals exist. For random variables, $Z_1\prec_{CXD}Z_2$ means this for their laws.
--   3. Two random variables $Y_1,Y_2$ are **comonotone** if their joint distribution function is the upper Fréchet bound,
--   $$\mathbb P\{Y_1\le u,\ Y_2\le v\}=\min\big(G_1(u),G_2(v)\big)\quad\text{for all }u,v,$$
--   where $G_i$ is the distribution function of $Y_i$.
--
--   A functional is comonotone additive if it is additive on comonotone pairs; the converse half of the Choquet representation is stated for such functionals.
--
--   **Formalization Note** "Both integrals exist" is read as integrability of $U$ under both laws. Uniformity is equality of the image measure $\mathbb P\circ U^{-1}$ with Lebesgue measure restricted to $[0,1]$, together with measurability of $U$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 14, Definition 1.10(iv); pp. 8–9, Definition 1.4(ii), Eq. (1.11)

import Mathlib
import Definitions.Def_RiskFunctionals_Distortion_QuantileFunction

namespace RiskFunctionals.Distortion

open MeasureTheory

/-- `U` is a uniform `[0, 1]` random variable on `(Ω, ℱ, P)`: `U` is measurable and its law is
Lebesgue measure on `[0, 1]`. -/
def IsUniform01 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → ℝ) : Prop :=
  Measurable U ∧ P.map U = volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Convex dominance `G₁ ≺_CXD G₂` (Pflug & Römisch, p. 14, Definition 1.10(iv)), for
distributions given as probability measures `μ₁`, `μ₂` on `ℝ`: `∫ U dG₁ ≤ ∫ U dG₂` for every
convex `U` for which both integrals exist. For random variables, `Z₁ ≺_CXD Z₂` means
`CXD (P.map Z₁) (P.map Z₂)`. -/
def CXD (μ₁ μ₂ : Measure ℝ) : Prop :=
  ∀ U : ℝ → ℝ, ConvexOn ℝ Set.univ U → Integrable U μ₁ → Integrable U μ₂ →
    ∫ v, U v ∂μ₁ ≤ ∫ v, U v ∂μ₂

/-- Two random variables `Y₁`, `Y₂` on `(Ω, ℱ, P)` are comonotone (Pflug & Römisch, pp. 8–9,
Definition 1.4, case (ii), (1.11)) if they are coupled with the upper Fréchet copula
`C(s, t) = min(s, t)`, i.e. their joint distribution function is
`P{Y₁ ≤ u, Y₂ ≤ v} = min(G₁(u), G₂(v))` for all `u, v`. -/
def Comonotone {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y₁ Y₂ : Ω → ℝ) : Prop :=
  ∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
    min (distributionFunction (P.map Y₁) u) (distributionFunction (P.map Y₂) v)

end RiskFunctionals.Distortion


