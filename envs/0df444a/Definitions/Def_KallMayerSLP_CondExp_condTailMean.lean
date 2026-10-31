-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_condTailMean
-- name    : KallMayerSLP_CondExp_condTailMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:10:25.065915+00:00
-- url     : https://prove2.me/theorems/aacbcec3-13dd-44d4-8feb-dff13c621f72
-- title:
--   Conditional tail mean $\mathbb E[\vartheta\mid\vartheta\ge z]$
-- statement:
--   For an integrable random variable $\vartheta$ and a level $z$ with $\mathbb P(\vartheta\ge z)>0$,
--   $$
--   \mathbb E[\vartheta\mid\vartheta\ge z]=\frac{1}{\mathbb P(\vartheta\ge z)}\int_{\{\vartheta\ge z\}}\vartheta\,d\mu .
--   $$
--   At a quantile level this is the mean of the upper tail, the quantity that CVaR equals for continuous distributions.
--
--   **Formalization Note** The book forms this only at quantiles, where the denominator is positive; every statement here is at such a level, so the Lean value at a zero denominator is never used.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.27), p.160

import Mathlib

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- The conditional expectation `𝔼[ϑ | ϑ ≥ z] := (1 / ℙ(ϑ ≥ z)) ∫_z^∞ t dF_ϑ(t)`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, first line of eq. (4.27), p.160
(PDF 170).

**Formalization Note** The book forms this only at quantiles `z`, where `ℙ(ϑ ≥ z) > 0`. Every
statement using `condTailMean` is at such a `z`; the Lean value `0` at `ℙ(ϑ ≥ z) = 0` is never used. -/
noncomputable def condTailMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ)
    (z : ℝ) : ℝ :=
  (∫ ω in {ω | z ≤ ϑ ω}, ϑ ω ∂μ) / μ.real {ω | z ≤ ϑ ω}

end KallMayerSLP.CondExp


