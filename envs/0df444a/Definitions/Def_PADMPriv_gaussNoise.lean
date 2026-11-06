-- Prove2me | Definitions.Def_PADMPriv_gaussNoise
-- name    : PADMPriv_gaussNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:23.415177+00:00
-- url     : https://prove2.me/theorems/cd0280b6-dc6e-4858-89d8-54f191a65156
-- title:
--   Gaussian noise law $N(0_m,\sigma^2 I_m)$
-- statement:
--   The privacy noise of PADM-$N_\sigma$ is drawn from the centred Gaussian law on $\mathbb R^m$ with covariance $\sigma^2 I_m$,
--   $$
--   N(0_m,\sigma^2 I_m) = \text{law of } \sigma Z,\qquad Z\sim N(0_m, I_m).
--   $$
--   Its second moment is $\mathbb E\|z\|_2^2 = m\sigma^2$.
--
--   **Formalization Note** The image of Mathlib's standard Gaussian measure on $\mathbb R^m$ under $z\mapsto\sigma z$; it is a probability measure for every $\sigma$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.2, p.10

import Mathlib

namespace PADMPriv

open MeasureTheory ProbabilityTheory

/-- The Gaussian noise law `N(0_m, σ²I_m)` on `ℝᵐ` of PADM-N_σ, Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Section 4.2, p.10: the image of the standard Gaussian measure on `ℝᵐ` under `z ↦ σz`.

**Formalization Note** `ℝᵐ` is `EuclideanSpace ℝ (Fin m)` and the standard Gaussian is Mathlib's
`stdGaussian`. -/
noncomputable def gaussNoise (m : ℕ) (σ : ℝ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  (stdGaussian (EuclideanSpace ℝ (Fin m))).map (fun z => σ • z)

instance gaussNoise_isProbabilityMeasure (m : ℕ) (σ : ℝ) :
    IsProbabilityMeasure (gaussNoise m σ) :=
  Measure.isProbabilityMeasure_map (measurable_const_smul σ).aemeasurable

end PADMPriv


