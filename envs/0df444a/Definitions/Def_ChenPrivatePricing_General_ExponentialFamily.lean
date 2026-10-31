-- Prove2me | Definitions.Def_ChenPrivatePricing_General_ExponentialFamily
-- name    : ChenPrivatePricing_General_ExponentialFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T06:40:43.239741+00:00
-- url     : https://prove2.me/theorems/0cbe3d76-38a1-46fe-8ac6-1c367d2426a7
-- title:
--   Scalar exponential family relative to a reference measure
-- statement:
--   An exponential family has an arbitrary reference measure on the real line, an explicit natural-parameter domain, scale zeta, cumulant m and base log-density h. Its density is exp(zeta(yz-m(z))+h(y)); its law is that density times the reference measure. Normalized means the density is measurable and has nonnegative extended integral one for each parameter in the domain. Discrete and continuous reference measures are allowed.
-- source:
--   Chen, Simchi-Levi and Wang, arXiv:2009.12920v2 (25 July 2021), p. 9, equation (1)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ChenPrivatePricing.General

/-- A scalar exponential family, relative to an arbitrary reference measure.
The parameter domain is explicit; normalization is not supplied by a default integral. -/
structure ExponentialFamily where
  reference : Measure ℝ
  domain : Set ℝ
  zeta : ℝ
  cumulant : ℝ → ℝ
  baseLogDensity : ℝ → ℝ

noncomputable def ExponentialFamily.density (E : ExponentialFamily) (z y : ℝ) : ℝ :=
  Real.exp (E.zeta * (y * z - E.cumulant z) + E.baseLogDensity y)

noncomputable def ExponentialFamily.law (E : ExponentialFamily) (z : ℝ) : Measure ℝ :=
  E.reference.withDensity (fun y => ENNReal.ofReal (E.density z y))

def ExponentialFamily.Normalized (E : ExponentialFamily) : Prop :=
  ∀ z ∈ E.domain, Measurable (E.density z) ∧
    ∫⁻ y, ENNReal.ofReal (E.density z y) ∂E.reference = 1

end ChenPrivatePricing.General


