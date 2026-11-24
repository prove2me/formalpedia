-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqThresholdKernel
-- name    : GrothendieckLB_Supplement_cqThresholdKernel
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T21:59:56.137584+00:00
-- url     : https://prove2.me/theorems/4fb5bf0d-6275-4bdb-bc27-d88d3eaa1335
-- title:
--   Shifted Gaussian threshold correlation for complex covariance
-- statement:
--   The threshold correlation averages the two shifted signs against the complex bivariate Gaussian density and uses the arcsine normalization. Its one-dimensional slice fixes the first coordinate on its threshold boundary. Averaging this correlation against the Gaussian for the reflected spatial coordinate gives the analytic form of the cubic–quintic scheme.
-- source:
--   Degree-251 fixed-point Hermite certificate for the cubic–quintic scheme of Saha et al., arXiv:2608.11158v2, and Prove2Me fc28e7f8-2588-498a-8ea6-e8d0e220ae2b.

import Definitions.Def_GrothendieckLB_Supplement_cqPriceKernels

open MeasureTheory
namespace GrothendieckLB.Supplement.CQThreshold
open CQPrice

/-- The sign of a real variable with an additive shift, with positive boundary value. -/
noncomputable def S (u x : ℝ) : ℂ := if -u≤x then 1 else -1

/-- The arcsine-normalized threshold correlation at complex covariance and real shifts. -/
noncomputable def K (q : ℂ) (u v : ℝ) : ℂ := ((Real.pi/2:ℝ):ℂ) *
  ∫ w : ℝ×ℝ, density q w.1 w.2*(S u w.1*S v w.2)

/-- One Gaussian coordinate fixed at the first threshold boundary. -/
noncomputable def J (q : ℂ) (u v : ℝ) : ℂ := ∫ y : ℝ, S v y*density q (-u) y

/-- Gaussian average of the shifted correlation at the cubic threshold and reflected spatial covariance. -/
noncomputable def H (z : ℂ) : ℂ := ∫ w : ℝ×ℝ, density (-z) w.1 w.2*
  K (eval rho z) (threshold w.1) (threshold w.2)

end GrothendieckLB.Supplement.CQThreshold


