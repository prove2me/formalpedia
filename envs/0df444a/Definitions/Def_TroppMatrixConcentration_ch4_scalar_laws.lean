-- Prove2me | Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws
-- name    : TroppMatrixConcentration_ch4_scalar_laws
-- status  : Definition
-- author  : @tc
-- created : 2026-10-07T13:45:13.687297+00:00
-- url     : https://prove2.me/theorems/95c0b38e-665e-4e0d-b790-a874cbc38df1
-- title:
--   Gaussian and Rademacher scalar laws; Gaussian-series tail
-- statement:
--   For a real function $g$ on a measure space with measure $\mu$, `standardGaussianLaw μ g` means its pushforward measure is the real Gaussian probability measure with mean zero and variance one. `rademacherLaw μ g` means its pushforward is $\tfrac12\delta_1+\tfrac12\delta_{-1}$. Measurability is imposed separately in theorem statements. For a natural dimension $d$ and real $v,t$, `gaussianSeriesTail d v t` is $d\exp(-t^2/(2v))$ when $v\ne0$. At $v=0$ it is $d$ if $t=0$ and zero otherwise. Concentration statements use this expression only for $v,t\ge0$ and positive dimensions. The piecewise definition avoids totalized division in the zero-series case; it assumes no bound on any random matrix.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Section 2.2.2, printed p. 26; Theorem 4.1.1, equations (4.1.3–6), printed p. 42; Theorem 4.6.1, printed p. 51.

import Definitions.Def_TroppMatrixConcentration_probability
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory

noncomputable section
namespace TroppMatrixConcentration

def standardGaussianLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (g : Ω → ℝ) : Prop :=
  Measure.map g μ = gaussianReal 0 1

def rademacherLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (r : Ω → ℝ) : Prop :=
  Measure.map r μ = (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)

def gaussianSeriesTail (dimension : ℕ) (v t : ℝ) : ℝ :=
  if v = 0 then (if t = 0 then (dimension : ℝ) else 0)
  else (dimension : ℝ) * Real.exp (-(t ^ 2) / (2 * v))

end TroppMatrixConcentration


