-- Prove2me | Definitions.Def_AppliedSDE_SarkkaSolin_OUKalmanInterfaces
-- name    : AppliedSDE_SarkkaSolin_OUKalmanInterfaces
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-13T10:16:18.784204+00:00
-- url     : https://prove2.me/theorems/025dee3f-376d-48cd-bd32-2cde2ebb0467
-- title:
--   Source-backed OU covariance, Kalman prediction/update and GP posterior interfaces
-- statement:
--   Särkkä and Solin (2019): Example 6.8 Eq. (6.75) defines the stationary scalar OU covariance q/(2rate) exp(-rate|s-t|); Eq. (6.24) gives the OU transition coefficient. Chapter 10 scalar Kalman prediction and update give the updated variance and gain, and Eq. (12.14) gives batch Gaussian-process regression. These are definitions of the chapter interfaces and do not themselves prove their stochastic correctness.
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Chapter 6 Example 6.8, Algorithm 10.9 and Chapter 12 Eqs. (12.13)–(12.14). https://doi.org/10.1017/9781108186735

import Mathlib
set_option autoImplicit false
open Matrix
open scoped BigOperators Matrix

namespace AppliedSDE.SarkkaSolin

/-- Särkkä–Solin Example 6.8, Eq. 6.75: stationary scalar OU covariance. -/
noncomputable def stationaryOUCovariance
    (rate q : ℝ) (s t : ℝ) : ℝ :=
  q / (2 * rate) * Real.exp (-rate * |s - t|)

/-- Särkkä–Solin Eq. 6.24: OU state transition factor for a step. -/
noncomputable def ouStepFactor (rate Δ : ℝ) : ℝ :=
  Real.exp (-rate * Δ)

/-- Särkkä–Solin Algorithm 10.9, scalar OU variance prediction. -/
noncomputable def ouPredictedVariance
    (rate q Δ currentVariance : ℝ) : ℝ :=
  let a := ouStepFactor rate Δ
  a ^ 2 * currentVariance + q / (2 * rate) * (1 - a ^ 2)

/-- Särkkä–Solin Algorithm 10.9, one noisy scalar variance update. -/
noncomputable def scalarUpdatedVariance
    (predicted observationVariance : ℝ) : ℝ :=
  predicted * observationVariance / (predicted + observationVariance)

/-- Särkkä–Solin Chapter 10, scalar Kalman innovation gain. -/
noncomputable def scalarKalmanGain
    (predicted observationVariance : ℝ) : ℝ :=
  predicted / (predicted + observationVariance)

/-- Särkkä–Solin Section 12.2, batch zero-mean GP regression posterior. -/
noncomputable def gpBatchPosteriorMean
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (observations : Fin n → ℝ) : Fin n → ℝ :=
  K.mulVec (((K + r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec observations)

end AppliedSDE.SarkkaSolin


