-- Prove2me | Definitions.Def_DistributionFreeInventory_TwoLocation_Moments
-- name    : DistributionFreeInventory_TwoLocation_Moments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:29:11.554988+00:00
-- url     : https://prove2.me/theorems/ba7aebee-707a-47d9-bf9f-cddc46479018
-- title:
--   Bivariate moment ambiguity and six-point probability laws
-- statement:
--   Demand lives in the real plane. The data are real means $m_i$, nonnegative standard deviations $\sigma_i$, and $-1\le\rho\le1$. The covariance matrix has diagonal $\sigma_i^2$ and off-diagonal $\rho\sigma_1\sigma_2$.
--
--   The ambiguity set $\mathcal F$ reuses the published mean–covariance class: all Borel probability laws with finite second coordinate moments, these means, and this covariance. Equivalently, their raw second moments are $m_i^2+\sigma_i^2$ and $m_1m_2+\rho\sigma_1\sigma_2$. No nonnegative support, independence, density, Gaussianity or finite support is required. When a standard deviation vanishes, $\rho$ specifies covariance instead of a defined Pearson correlation.
--
--   A six-point law is $\sum_{k=1}^6w_k\delta_{x_k}$ with $w_k\ge0$, $\sum_kw_k=1$, and $x_k\in\mathbb R^2$. Zero weights and repeated points are allowed, so this means at most six support points. Lean uses EuclideanSpace and zero-based `Fin` indices.
-- source:
--   Govindarajan, Sinha & Uichanco, Distribution-Free Inventory Risk Pooling in a Multilocation Newsvendor, DOI 10.1287/mnsc.2020.3719, held source.pdf, §3–4, printed pp. 11, 13–16 (PDF 11, 13–16); Table EC.3, ec8 (PDF 41)

import Definitions.Def_RobustMeanCov_Projection_MeanCovClass
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace DistributionFreeInventory.TwoLocation

abbrev Demand := EuclideanSpace ℝ (Fin 2)

/-- Moment parameters; correlation at a zero variance is a covariance parameter. -/
structure Moments where
  mean : Demand
  sigma : Fin 2 → ℝ
  rho : ℝ
  sigma_nonneg : ∀ i, 0 ≤ sigma i
  rho_lower : -1 ≤ rho
  rho_upper : rho ≤ 1

/-- Diagonal variances and the given cross covariance, including singular matrices. -/
def covariance (M : Moments) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then M.sigma i ^ 2 else M.rho * M.sigma 0 * M.sigma 1

/-- All Borel moment laws, reusing the published finite-second-moment class. -/
def ambiguity (M : Moments) : Set (Measure Demand) :=
  RobustMeanCov.Projection.MeanCovClass M.mean (covariance M)

/-- Exactly six slots, allowing zero mass and coincident atoms. -/
def SixPointLaw (μ : Measure Demand) : Prop :=
  ∃ (w : Fin 6 → NNReal) (x : Fin 6 → Demand),
    (∑ k, w k) = 1 ∧ μ = ∑ k, (w k : ℝ≥0∞) • Measure.dirac (x k)

end DistributionFreeInventory.TwoLocation


