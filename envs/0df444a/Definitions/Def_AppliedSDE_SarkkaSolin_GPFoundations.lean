-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_GPFoundations
-- name    : AppliedSDE_SarkkaSolin_GPFoundations
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T17:49:06.300134+00:00
-- url     : https://prove2.me/theorems/c77797cf-cc05-4540-a07f-19f10b465f53
-- title:
--   Särkkä–Solin GP mean, covariance, Gaussian, stationary, isotropic and separable definitions
-- statement:
--   Source-faithful definitions from Särkkä and Solin (2019), Chapter 12, Definitions 12.1–12.5, printed pp. 252–253. The Gaussian-process predicate represents every finite-dimensional marginal as an affine linear image of standard independent Gaussian variables. The mean and covariance integrals are defined explicitly. Stationarity requires a constant mean and lag-dependent covariance; isotropy requires dependence on Euclidean distance; separability requires a product of kernels on distinct input axes. Integrability assumptions are required in the theorems using these integrals.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   m(t)=\mathbb E[f(t)],\qquad K(s,t)=\operatorname{Cov}(f(s),f(t))
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Definitions 12.1–12.5, pp. 252–253. https://doi.org/10.1017/9781108186735

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AppliedSDE.SarkkaSolin

/-- Särkkä–Solin Definition 12.2: the mean function of a real random field. -/
noncomputable def gpMean {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) (t : ι) : ℝ :=
  ∫ ω, X t ω ∂P

/-- Särkkä–Solin Definition 12.2: the centred covariance kernel. -/
noncomputable def gpCovariance {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) (s t : ι) : ℝ :=
  ∫ ω, (X s ω - gpMean P X s) * (X t ω - gpMean P X t) ∂P

/-- Särkkä–Solin Definition 12.1: every finite indexed subfamily has a Gaussian law.
The representation allows singular covariance matrices through a linear factor. -/
def IsGaussianProcess {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ (n : ℕ) (times : Fin n → ι),
    ∃ (mean : Fin n → ℝ)
      (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)),
      Measure.map (fun ω : Ω => fun k : Fin n => X (times k) ω) P =
        Measure.map (fun z : Fin n → ℝ => mean + L z)
          (Measure.pi (fun _ : Fin n => gaussianReal 0 1))

/-- Särkkä–Solin Definition 12.3: a Gaussian process with constant mean
and translation-invariant covariance function. -/
def IsStationaryGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → ℝ) : Prop :=
  IsGaussianProcess P X ∧
    ∃ (m : ℝ) (c : ℝ → ℝ),
      (∀ t : ℝ, gpMean P X t = m) ∧
      (∀ s t : ℝ, gpCovariance P X s t = c (s - t))

/-- Särkkä–Solin Definition 12.4: covariance depends only on Euclidean distance. -/
def IsIsotropicCovariance {d : ℕ}
    (C : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) : Prop :=
  ∃ c : ℝ → ℝ, ∀ x y, C x y = c ‖x - y‖

/-- Särkkä–Solin Definition 12.5: a product covariance on disjoint input axes.
This records the prose definition, independently of illustrative examples. -/
def IsSeparableCovariance {d e : ℕ}
    (C : ((Fin d → ℝ) × (Fin e → ℝ)) →
         ((Fin d → ℝ) × (Fin e → ℝ)) → ℝ) : Prop :=
  ∃ (C₁ : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (C₂ : (Fin e → ℝ) → (Fin e → ℝ) → ℝ),
    ∀ x y, C x y = C₁ x.1 y.1 * C₂ x.2 y.2

end AppliedSDE.SarkkaSolin


