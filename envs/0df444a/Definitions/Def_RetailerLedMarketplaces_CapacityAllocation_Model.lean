-- Prove2me | Definitions.Def_RetailerLedMarketplaces_CapacityAllocation_Model
-- name    : RetailerLedMarketplaces_CapacityAllocation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:26.975855+00:00
-- url     : https://prove2.me/theorems/b2f6de43-133f-4247-bc6f-94ab86e84dcf
-- title:
--   Product distribution and fixed-fee marketplace parameters
-- statement:
--   Let $c\ge0$ be common unit cost, $f\in[0,1]$ the ad valorem fee and $\lambda\in[0,1]$ the steerable consumer share. Products have a probability law $\mu$ on the real line, with a measurable nonnegative density $g$ relative to Lebesgue measure. Its cumulative distribution is computed as
--
--   $$G(v)=\mu(( -\infty,v]),\qquad \mu(( -\infty,c])=0.$$
--
--   The density may vanish on intervals, the support may be bounded, and the first moment may be infinite. A measurable representative with extended density values changes no absolutely continuous probability law. Assumption 1, $\lambda\ge1/2$, is imposed only in the results that use it, rather than inside the parameter structure.
--
--   These primitives share the published actual-demand pricing game and its per-product algebra, with no optimizer or threshold-existence assumption. The published real aggregate-profit integral is not used.
-- source:
--   Hervas-Drane and Shelegia, Retailer-Led Marketplaces, Management Science, Articles in Advance (2025), doi:10.1287/mnsc.2023.00315, printed pp. 4–6 (PDF pp. 6–8), Sections 2–4 and Assumption 1

import Definitions.Def_RetailerMarketplace_Entry_PricingGame
import Definitions.Def_RetailerMarketplace_Entry_Model

open MeasureTheory Set
noncomputable section

namespace RetailerLedMarketplaces.CapacityAllocation

/-- Fixed fee continuation parameters; Assumption 1 is not bundled here. -/
structure Parameters where
  c : ℝ
  f : ℝ
  lam : ℝ
  cost_nonneg : 0 ≤ c
  fee_range : f ∈ Icc 0 1
  steering_range : lam ∈ Icc 0 1

/-- A unit mass with a density, G(c)=0. No support positivity or moment assumption. -/
structure ProductLaw (c : ℝ) where
  measure : Measure ℝ
  density : ℝ → ENNReal
  density_measurable : Measurable density
  has_density : measure = volume.withDensity density
  probability : IsProbabilityMeasure measure
  below_cost : measure (Iic c) = 0

/-- Reuse the published computed CDF, never a free variable for the CDF. -/
def cdf {c : ℝ} (d : ProductLaw c) (v : ℝ) : ℝ :=
  RetailerMarketplace.Entry.G d.measure v

end RetailerLedMarketplaces.CapacityAllocation


