-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior_measure
-- name    : InfoBargaining_SellerPayoff_FocalPrior_measure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:19.454486+00:00
-- url     : https://prove2.me/theorems/4f73693c-2e9b-4bdf-93e1-fa0c8c2f97fa
-- title:
--   Prior law of the buyer's value under each focal distribution
-- statement:
--   The prior law $\mu_P$ of the buyer's value $u$ for each focal distribution $P$:
--
--   1. uniform: Lebesgue measure on $[0,1]$, so $F(u)=u$;
--   2. exponential with mean $\hat u$: the exponential law of rate $1/\hat u$, density $\hat u^{-1}e^{-u/\hat u}$ on $u\ge0$, so $F(u)=1-e^{-u/\hat u}$;
--   3. logistic with location $\hat u$: density $e^{-(u-\hat u)}/(1+e^{-(u-\hat u)})^2$ on $\mathbb R$, the derivative of $F(u)=1/[1+e^{-(u-\hat u)}]$;
--   4. modified pareto with parameter $\lambda$: the Beta$(1,\lambda)$ law, density $\lambda(1-u)^{\lambda-1}$ on $(0,1)$, so $F(u)=1-(1-u)^\lambda$ on $[0,1]$.
--
--   **Formalization Note** The modified pareto law is Mathlib's `betaMeasure 1 λ`, not Mathlib's `paretoMeasure` (the classical Pareto law). Mathlib has no logistic law, so it is defined through its density.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.2, p. 13 (uniform); proof of Corollary 1, p. 30 (exponential, logistic, modified pareto)

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_FocalPrior

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The prior law of the buyer's value `u` under each focal distribution.**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
p. 13 (uniform) and proof of Corollary 1, p. 30 (exponential, logistic, modified pareto).

* `uniform ↦` Lebesgue measure restricted to `[0, 1]` (`F(u) = u` on `[0, 1]`);
* `exponential û ↦ expMeasure (1/û)`, the exponential law of rate `1/û`, density
  `(1/û) e^{−u/û}` on `u ≥ 0`, i.e. `F(u) = 1 − e^{−u/û}`;
* `logistic û ↦` Lebesgue measure with density `e^{−(u−û)}/(1 + e^{−(u−û)})²`, the derivative
  of `F(u) = 1/[1 + e^{−(u−û)}]` (location `û`, scale `1`, as printed);
* `modPareto λ ↦ betaMeasure 1 λ`, density `λ(1 − u)^{λ−1}` on `(0, 1)`, i.e.
  `F(u) = 1 − (1 − u)^λ` on `[0, 1]`.

**Formalization Note.** The modified pareto law is Mathlib's Beta(1, λ) law, not Mathlib's
`paretoMeasure` (the classical Pareto). Mathlib has no logistic law, so it is written with
`withDensity`. -/
noncomputable def FocalPrior.measure : FocalPrior → Measure ℝ
  | .uniform => (volume : Measure ℝ).restrict (Set.Icc 0 1)
  | .exponential uhat _ => ProbabilityTheory.expMeasure (1 / uhat)
  | .logistic uhat _ => (volume : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (Real.exp (-(u - uhat)) / (1 + Real.exp (-(u - uhat))) ^ 2))
  | .modPareto lam _ => ProbabilityTheory.betaMeasure 1 lam

end InfoBargaining.SellerPayoff


