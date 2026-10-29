-- Prove2me | Definitions.Def_CohenPriceFairness_LocalWelfare_Market
-- name    : CohenPriceFairness_LocalWelfare_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:36.02718+00:00
-- url     : https://prove2.me/theorems/cebb0735-39e9-4fcf-b706-3792ecd2672f
-- title:
--   Two-group market, purchase probability, profit, and welfare
-- statement:
--   A market consists of two marginal Borel measures $\mu_i$ on the real line, real population masses $d_i$, and common real marginal cost $c$, for $i\in\{0,1\}$. An admissible market has $c\ge0$, $d_i>0$, and each marginal is a nonnegative valuation law with finite first moment. No joint distribution or independence is required, and populations are not normalized.
--
--   At real price $p$, define $q_i(p)=\mu_i([p,\infty))$, $S_i(p)=\int\max(v-p,0)\,d\mu_i(v)$ and $R_i(p)=d_i(p-c)q_i(p)$. The nonbuyer mean is $N_i(p)=\int_{v<p}v\,d\mu_i/\mu_i(( -\infty,p))$ when the conditioning event has positive mass, and is explicitly zero when its mass is zero. A price vector has two real coordinates; the feasible domain is imposed separately.
--
--   Total profit is $R_0(p_0)+R_1(p_1)$ and welfare is this total plus $d_0S_0(p_0)+d_1S_1(p_1)$. This uses the intended group-specific surplus indices on pp. 7 and 31, rather than the duplicated subscript on pp. 8 and 12. The definitions are total on raw market data, but theorem uses require either admissibility or the explicit uniform/exponential laws, which ensure finite genuine expectations.
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; §§2–2.1, pp. 6–8; group welfare on p. 7 and proof on p. 31.

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

/- Imported definition source (verbatim dependency snapshot for standalone inspection).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare
-/


