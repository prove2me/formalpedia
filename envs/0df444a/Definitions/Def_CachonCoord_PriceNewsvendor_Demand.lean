-- Prove2me | Definitions.Def_CachonCoord_PriceNewsvendor_Demand
-- name    : CachonCoord_PriceNewsvendor_Demand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:06:02.535471+00:00
-- url     : https://prove2.me/theorems/0b9f1fc6-f856-44b1-818e-d0806e00121b
-- title:
--   §6.3.1, pp. 33–34 — price-indexed demand laws and their distribution functions
-- statement:
--   A **price-indexed demand family** assigns a probability law $D_p$ to each admissible retail price $p$ in a nonempty open set $P$. The distribution function is $F(y\mid p)=\Pr_{D_p}(D\le y)$. Demand is nonnegative, has no mass at zero, and has a finite mean. On nonnegative demand levels the distribution function is strictly increasing and differentiable. At positive demand levels its price derivative exists and is positive:
--
--   $$\frac{\partial F(y\mid p)}{\partial p}>0\qquad(y>0,\ p\in P).$$
--
--   This is the chapter's stochastic-decrease assumption: a higher price shifts demand downward. The family supplies the probability laws used by expected sales and mean demand in the contract model.
--
--   **Formalization Note** The support, no-zero-mass and finite-mean conditions encode the newsvendor model inherited from §6.2. Openness of $P$ makes the price first-order conditions interior statements. The strict price derivative is imposed at $y>0$, since $F(0\mid p)=0$ for every admissible price.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §§6.2.1 and 6.3.1, pp. 7, 33–34

import Mathlib

namespace CachonCoord.PriceNewsvendor

/-- The distribution function of a real-valued demand law. -/
noncomputable def cdfOf (ν : MeasureTheory.Measure ℝ) (y : ℝ) : ℝ :=
  (ν (Set.Iic y)).toReal

/-- Price-indexed, nonnegative demand in §6.3. Prices are chosen from a nonempty open set.
The price derivative records the chapter's stochastic decrease of demand as price rises. -/
structure DemandFamily where
  prices : Set ℝ
  prices_nonempty : prices.Nonempty
  prices_open : IsOpen prices
  law : ℝ → MeasureTheory.Measure ℝ
  probability : ∀ p ∈ prices, MeasureTheory.IsProbabilityMeasure (law p)
  nonnegative : ∀ p ∈ prices, law p (Set.Iio 0) = 0
  no_zero_mass : ∀ p ∈ prices, law p ({0} : Set ℝ) = 0
  finite_mean : ∀ p ∈ prices, MeasureTheory.Integrable (fun d : ℝ => d) (law p)
  cdf_strict : ∀ p ∈ prices, StrictMonoOn (cdfOf (law p)) (Set.Ici 0)
  cdf_differentiable : ∀ p ∈ prices, ∀ y : ℝ, 0 < y →
    DifferentiableAt ℝ (cdfOf (law p)) y
  priceSlope : ℝ → ℝ → ℝ
  price_derivative : ∀ p ∈ prices, ∀ y : ℝ, 0 < y →
    HasDerivAt (fun t => cdfOf (law t) y) (priceSlope y p) p
  price_slope_pos : ∀ p ∈ prices, ∀ y : ℝ, 0 < y → 0 < priceSlope y p

end CachonCoord.PriceNewsvendor


