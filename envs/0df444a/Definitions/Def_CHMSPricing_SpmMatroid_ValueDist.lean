-- Prove2me | Definitions.Def_CHMSPricing_SpmMatroid_ValueDist
-- name    : CHMSPricing_SpmMatroid_ValueDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:56:15.453697+00:00
-- url     : https://prove2.me/theorems/610e3081-ef36-4419-aedc-7731a21d5278
-- title:
--   Value distributions with a density on a bounded interval, virtual values, regularity, the product prior
-- statement:
--   Each agent's private value $v_i$ is drawn from a distribution $F_i$ with density $f_i$ (§2.1). Here a **value distribution** is given by a support interval $[\underline{v}, \overline{v}]$ with $0 \le \underline{v} < \overline{v}$ and a measurable density $f$ that is strictly positive on $[\underline{v}, \overline{v}]$ and integrates to $1$ over it; the law of the value is the measure with density $f$ on $[\underline{v}, \overline{v}]$ and no mass outside. Its distribution function is $F(x) = \Pr[v \le x]$.
--
--   For such a distribution the **virtual valuation** (Definition 1) is
--
--   $$\phi(v) = v - \frac{1 - F(v)}{f(v)},$$
--
--   and the distribution is **regular** (Definition 2) if $\phi$ is monotone non-decreasing on the support $[\underline{v}, \overline{v}]$.
--
--   For $n$ agents with value distributions $F_1, \dots, F_n$, the **type space** is the box $\prod_i [\underline{v}_i, \overline{v}_i]$, and the **prior** is the product measure $F_1 \times \cdots \times F_n$: values are independent.
--
--   These objects are the probabilistic side of the Bayesian single-parameter mechanism design problem (BSMD) and are used by every statement of the mission.
--
--   **Formalization Note** The paper only says "distribution function $F_i$ with density $f_i$". The bounded support with a positive density on it is a modelling pin: it rules out point masses (as §4 assumes for the main construction) and makes $F_i$ continuous and strictly increasing on the support, so $F_i^{-1}$ is well defined there. Regularity is monotonicity of $\phi$ on the support only, where $f > 0$. Each agent has its own support.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1; p. 12, Definitions 1–2

import Mathlib

namespace CHMSPricing.SpmMatroid

open MeasureTheory

/-- A value distribution with density `f`, measurable and strictly positive on the bounded
interval `[lo, hi]` (`0 ≤ lo < hi`), integrating to `1` there and putting no mass outside
(standing pin P1 for "distribution function `F` with density `f`", §2.1, p. 4). -/
structure ValueDist where
  lo : ℝ
  hi : ℝ
  f : ℝ → ℝ
  lo_nonneg : 0 ≤ lo
  lo_lt_hi : lo < hi
  f_measurable : Measurable f
  f_pos : ∀ x ∈ Set.Icc lo hi, 0 < f x
  f_intervalIntegrable : IntervalIntegrable f volume lo hi
  f_integral : ∫ x in lo..hi, f x = 1

namespace ValueDist

/-- The law of the value: density `f` on `[lo, hi]`, no mass outside. -/
noncomputable def law (D : ValueDist) : Measure ℝ :=
  (volume.restrict (Set.Icc D.lo D.hi)).withDensity (fun x => ENNReal.ofReal (D.f x))

/-- The distribution function `F(x) = Pr[v ≤ x]`. -/
noncomputable def cdf (D : ValueDist) (x : ℝ) : ℝ := (D.law (Set.Iic x)).toReal

/-- Definition 1 (p. 12): the virtual valuation `φ(v) = v − (1 − F(v)) / f(v)`. -/
noncomputable def virtualValue (D : ValueDist) (x : ℝ) : ℝ := x - (1 - D.cdf x) / D.f x

/-- Definition 2 (p. 12): `F` is regular if `φ` is monotone non-decreasing (on the support). -/
def Regular (D : ValueDist) : Prop := MonotoneOn D.virtualValue (Set.Icc D.lo D.hi)

end ValueDist

/-- The type space `∏ᵢ [loᵢ, hiᵢ]` of value profiles. -/
def typeSpace {ι : Type*} (D : ι → ValueDist) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (D i).lo (D i).hi)

/-- The common prior: the values `vᵢ ∼ Fᵢ` are drawn independently (product measure). -/
noncomputable def prior {ι : Type*} [Fintype ι] (D : ι → ValueDist) : Measure (ι → ℝ) :=
  Measure.pi (fun i => (D i).law)

end CHMSPricing.SpmMatroid


