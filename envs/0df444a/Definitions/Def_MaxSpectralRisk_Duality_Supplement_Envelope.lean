-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope
-- name    : MaxSpectralRisk_Duality_Supplement_Envelope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:06:09.025372+00:00
-- url     : https://prove2.me/theorems/ac7d7ea5-c6ca-45f0-b062-2aa57bf98705
-- title:
--   §5.1 — the expected-shortfall risk envelope Gα
-- statement:
--   Let $\mathcal W$ be a measurable space and $\pi\in\mathcal P(\mathcal W)$. For a confidence level $\alpha\in(0,1)$, define
--   $$
--   G_\alpha(\pi)=\{\Theta\in\mathcal P(\mathcal W):\Theta\ll\pi,\ d\Theta/d\pi\le (1-\alpha)^{-1}\ \pi\text{-a.s.}\}.
--   $$
--   The formal definition uses the equivalent finite setwise domination $\Theta\le (1-\alpha)^{-1}\pi$. Probability normalisation is part of the carrier of both arguments. This is the feasible risk envelope whose continuity is asserted in Theorem 2.
--
--   **Formalization Note** All uses assume $0<\alpha<1$. For finite measures and a finite nonnegative bound, domination is equivalent to absolute continuity and the almost-everywhere Radon–Nikodym bound. The weak topology is Mathlib's topology on probability measures.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 14, §5.1, display defining Gα

import Mathlib

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory

/-- §5.1, p. 14: the expected-shortfall envelope. The finite setwise bound is
 equivalent to absolute continuity and the stated a.e. Radon–Nikodym bound.
 Both arguments are probability measures. Theorems require 0 < α < 1. -/
def Galpha {W : Type*} [MeasurableSpace W] (α : ℝ)
    (π : ProbabilityMeasure W) : Set (ProbabilityMeasure W) :=
  {Θ | (Θ : Measure W) ≤ ENNReal.ofReal ((1 - α)⁻¹) • (π : Measure W)}

end MaxSpectralRisk.Duality.Supplement


