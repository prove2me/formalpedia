-- Prove2me | Definitions.Def_CohenPriceFairness_LocalWelfare_Families
-- name    : CohenPriceFairness_LocalWelfare_Families
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:28.576051+00:00
-- url     : https://prove2.me/theorems/e5e1ff97-fcf4-4157-8431-9838a2e53cb9
-- title:
--   Uniform and exponential valuation families with unequal parameters
-- statement:
--   For $b>0$, the uniform law on $[0,b]$ is normalized restricted Lebesgue measure, $b^{-1}\,\mathrm{Leb}|_{[0,b]}$. A two-group market has one of the two source families if either both marginal laws are uniform on $[0,b_i]$, where $b_i>0$ and $b_0\ne b_1$, or both are exponential laws of rates $\lambda_i>0$ with $\lambda_0\ne\lambda_1$. The exponential law is Mathlib's probability measure with density $\lambda e^{-\lambda v}$ for $v\ge0$ and zero elsewhere. The choice of family is common to both groups; parameters are otherwise arbitrary. No population or cost constraint is bundled into this predicate, and it imposes no property of optimal prices.
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; Theorem 2, p. 12; Table 2, p. 30; §3, p. 13.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Market

open MeasureTheory ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare

/-- Uniform probability on [0,b] for positive b: normalized restricted Lebesgue measure. -/
noncomputable def uniformLaw (b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal b)⁻¹ • volume.restrict (Set.Icc 0 b)

/-- Both groups use the same one of the two continuous families, with unequal parameters. -/
def Families (m : Market) : Prop :=
  (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧
    ∀ i, m.law i = uniformLaw (b i)) ∨
  (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
    ∀ i, m.law i = expMeasure (rate i))

end CohenPriceFairness.LocalWelfare

/- Imported definition source (verbatim dependency snapshot for standalone inspection).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_ValuationLaw

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- Two marginal valuation laws, real population masses, and common marginal cost. -/
structure Market where
  law : Fin 2 → Measure ℝ
  population : Fin 2 → ℝ
  cost : ℝ

/-- The general distribution-based market conventions, pp. 6–7. -/
def Market.Admissible (m : Market) : Prop :=
  0 ≤ m.cost ∧ ∀ i, 0 < m.population i ∧ ValuationLaw (m.law i)

noncomputable def demand (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  (m.law i (Set.Ici p)).toReal

noncomputable def surplus (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  ∫ v, max (v - p) 0 ∂m.law i

/-- Conditional mean of nonbuyers; explicitly zero on a null conditioning event. -/
noncomputable def nonbuyer (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  if m.law i (Set.Iio p) = 0 then 0
  else (∫ v in Set.Iio p, v ∂m.law i) / (m.law i (Set.Iio p)).toReal

noncomputable def profit (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  m.population i * (p - m.cost) * demand m i p

abbrev Prices := Fin 2 → ℝ

noncomputable def totalProfit (m : Market) (p : Prices) : ℝ :=
  profit m 0 (p 0) + profit m 1 (p 1)

/-- Group-specific surplus indices, as on pp. 7 and 31. -/
noncomputable def welfare (m : Market) (p : Prices) : ℝ :=
  totalProfit m p + m.population 0 * surplus m 0 (p 0) +
    m.population 1 * surplus m 1 (p 1)

end CohenPriceFairness.LocalWelfare
-/


