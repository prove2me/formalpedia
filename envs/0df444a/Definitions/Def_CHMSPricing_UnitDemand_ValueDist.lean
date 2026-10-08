-- Prove2me | Definitions.Def_CHMSPricing_UnitDemand_ValueDist
-- name    : CHMSPricing_UnitDemand_ValueDist
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:58:05.822282+00:00
-- url     : https://prove2.me/theorems/e19fb8c1-3ada-403a-a0c8-85742dfcfc02
-- title:
--   Value distributions with a density on a bounded interval, virtual values, regularity, the type space and the product prior
-- statement:
--   A **value distribution** $F$ is given by a density $f$ that is measurable and strictly positive on a bounded interval $[\underline v, \overline v]$ with $0 \le \underline v < \overline v$, integrates to $1$ over that interval, and puts no mass outside it. Its law is the measure with density $f$ on $[\underline v, \overline v]$, and its distribution function is $F(x) = \Pr[v \le x]$.
--
--   Following Definition 1 of the paper, the **virtual valuation** is
--   $$\phi(v) = v - \frac{1 - F(v)}{f(v)},$$
--   and (Definition 2) the distribution is **regular** if $\phi$ is monotone non-decreasing on $[\underline v, \overline v]$.
--
--   For a finite family of agents (or services) $i$ with distributions $F_i$, the **type space** is the box $\prod_i [\underline v_i, \overline v_i]$ of value profiles, and the **prior** is the product measure $\bigotimes_i F_i$: the values are drawn independently.
--
--   These objects are shared by the single-parameter instance $\mathcal I^{\mathrm{copies}}$ and the multi-parameter unit-demand instance $\mathcal I$ of the mission.
--
--   **Formalization Note** The paper only says "distribution function $F_i$ with density $f_i$" (§2.1, p. 4). The formalization pins this down as a density that is positive on a bounded interval of nonnegative values (pin P1). Regularity is monotonicity on the support, not strict monotonicity.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (independent values with densities); p. 12, Definitions 1–2

import Mathlib

namespace CHMSPricing.UnitDemand

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

end CHMSPricing.UnitDemand


