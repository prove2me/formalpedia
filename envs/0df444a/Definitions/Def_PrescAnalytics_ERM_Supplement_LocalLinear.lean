-- Prove2me | Definitions.Def_PrescAnalytics_ERM_Supplement_LocalLinear
-- name    : PrescAnalytics_ERM_Supplement_LocalLinear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:52:32.727911+00:00
-- url     : https://prove2.me/theorems/6b8aa255-ba23-4467-9d73-bb3f3c64887d
-- title:
--   Signed and clipped local-linear weights
-- statement:
--   Let $k_i=K((x^i-x)/h_N)$ and $\Xi=\sum_i k_i(x^i-x)(x^i-x)^T$. Put
--   $$a_i=k_i\left(1-\sum_j k_j(x^j-x)^T\Xi^{-1}(x^i-x)\right).$$
--   Equation (15) normalizes these signed numerators. Equation (16) clips the parenthesized correction at zero before normalization. The two methods remain distinct. The matrix inverse is zero when singular, and a zero normalizer gives zero weights. Eventual invertibility, positivity and normalization are proof obligations rather than premises.
-- source:
--   Bertsimas, Kallus, From Predictive to Prescriptive Analytics, arXiv:1402.5481v4, p. 11, Eqs. (15), (16)

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Supplement_Kernel

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace PrescAnalytics.ERM.Supplement

/-- The matrix Ξ of (15), in Euclidean coordinates. -/
noncomputable def localMatrix {dx : ℕ} (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N : ℕ) : Matrix (Fin dx) (Fin dx) ℝ :=
  fun a b => ∑ i ∈ Finset.range N,
    kernelScore K C δ xs x N i * (xs i - x) a * (xs i - x) b

/-- The linear correction in (15). Matrix.inv returns zero on singular real matrices. -/
noncomputable def localCorrection {dx : ℕ} (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ :=
  1 - ∑ j ∈ Finset.range N, kernelScore K C δ xs x N j *
    (∑ a : Fin dx, ∑ b : Fin dx,
      (xs j - x) a * (localMatrix K C δ xs x N)⁻¹ a b * (xs i - x) b)

/-- clip=false is signed (15); clip=true is nonnegative (16). -/
noncomputable def localScore {dx : ℕ} (clip : Bool) (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ :=
  kernelScore K C δ xs x N i *
    (if clip then max (localCorrection K C δ xs x N i) 0
     else localCorrection K C δ xs x N i)

/-- No clipping in the signed method; division by zero is totalized as zero. -/
noncomputable def localWeight {dx : ℕ} (clip : Bool) (K : KernelKind) (C δ : ℝ)
    (xs : ℕ → EuclideanSpace ℝ (Fin dx)) (x : EuclideanSpace ℝ (Fin dx))
    (N i : ℕ) : ℝ :=
  if i < N then localScore clip K C δ xs x N i /
    (∑ j ∈ Finset.range N, localScore clip K C δ xs x N j) else 0

end PrescAnalytics.ERM.Supplement


