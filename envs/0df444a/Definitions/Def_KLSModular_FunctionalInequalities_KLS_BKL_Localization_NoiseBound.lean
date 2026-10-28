-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:14:01.35301+00:00
-- url     : https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72
-- title:
--   Conjugated noise matrices
-- statement:
--   For a compactly supported probability measure $\mu$ and parameter $p$, `conjugatedNoiseMatrix μ hc p i` is the matrix whose $(a,b)$ entry is the third cumulant of the compact posterior at $p$, evaluated on the whitened basis vectors $A(p)^{-1/2}e_a$, $A(p)^{-1/2}e_b$, and $A(p)^{-1/2}e_i$. The definition is indexed by $i\in\mathrm{Fin}\,n$ and uses the covariance operator and its inverse square root. It is a coefficient object for the noise bound; the surrounding module documentation refers to further identities and estimates not provided by this declaration.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.Coefficients
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Localization.Standardization
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def conjugatedNoiseMatrix (p : Param n) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
--     Matrix.of fun a b =>
--       cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 3
--         ![inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ a),
--           inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ b),
--           inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i)]
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Standardization`](https://prove2.me/theorems/d6ac7b3b-4286-4c25-abe4-12ef241d0c20), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa).
--
--   Theorems in source order:
--
--   - [`cumulant_middle_sum`](https://prove2.me/theorems/9e0a41d8-8c46-4618-8921-3e596dfd076a)
--   - [`cumulantEnergy_succ_eq`](https://prove2.me/theorems/a8033ec2-2b13-4f3a-8086-a0cc4a62b333)
--   - [`sum_sq_conjugatedNoiseMatrix_mulVec_le`](https://prove2.me/theorems/bd7bc76e-3a86-4f3a-8622-a29d176bc214)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean) · `FunctionalInequalities.KLS.BKL.Localization.NoiseBound` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L187-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.NoiseBound`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Standardization
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities
namespace KLS
namespace BKL
variable {n : ℕ}
namespace Localization
variable (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
/-- The conjugated noise matrices `H̃_i = A^{-1/2} H_i A^{-1/2}` of BKL (85): entries
`κ₃(μ_p)(σ e_a, σ e_b, σ e_i)` with `σ = A(p)^{-1/2}`. -/
def conjugatedNoiseMatrix (p : Param n) (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b =>
    cumulant (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 3
      ![inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ a),
        inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ b),
        inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ i)]
end Localization
end BKL
end KLS
end FunctionalInequalities


