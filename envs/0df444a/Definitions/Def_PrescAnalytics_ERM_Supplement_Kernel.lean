-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_Kernel
-- name    : PrescAnalytics_ERM_Supplement_Kernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:51:17.469084+00:00
-- url     : https://prove2.me/theorems/8583bfb2-f3de-49fe-8f10-2987cec22ea6
-- title:
--   The three radial kernels and normalized kernel weights
-- statement:
--   Let $K$ be the naïve, Epanechnikov, or tri-cubic radial kernel on Euclidean covariate space, with the unit ball included in its support. At sample size $N$, let $h_N=CN^{-\delta}$. The normalized kernel weights are
--   $$w_{N,i}(x)=\frac{K((x^i-x)/h_N)}{\sum_{j=1}^N K((x^j-x)/h_N)}.$$
--   These weights reuse the published weighted objective. Zero denominators yield zero weights, and indices outside the sample have weight zero. Sample index $i$ in Lean corresponds to observation $i+1$ in the paper.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, pp. 10, 19, Eq. (13)

import Mathlib
import Definitions.Def_PrescAnalytics_KNN_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- The three radial kernels of §2.2, p. 10. -/
inductive KernelKind where
  | naive | epanechnikov | tricubic
  deriving DecidableEq

/-- All norms are Euclidean, including the radial cut-off. -/
noncomputable def kernel {d : ℕ} (K : KernelKind) (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖u‖ ≤ 1 then
    match K with
    | .naive => 1
    | .epanechnikov => 1 - ‖u‖ ^ 2
    | .tricubic => (1 - ‖u‖ ^ 3) ^ 3
  else 0

/-- Bandwidth at sample size N; h₀=0 under Real.rpow's convention for δ>0. -/
noncomputable def bandwidth (C δ : ℝ) (N : ℕ) : ℝ := C * (N : ℝ) ^ (-δ)

/-- The numerator of (13). -/
noncomputable def kernelScore {dx : ℕ} (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ := kernel K ((bandwidth C δ N)⁻¹ • (xs i - x))

/-- Normalized weights (13). A zero normalizer gives zero weights, not an arbitrary law. -/
noncomputable def kernelWeight {dx : ℕ} (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ :=
  if i < N then kernelScore K C δ xs x N i /
    (∑ j ∈ Finset.range N, kernelScore K C δ xs x N j) else 0

end PrescAnalytics.ERM.Supplement


