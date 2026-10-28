-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:15:49.512156+00:00
-- url     : https://prove2.me/theorems/736f8a3e-ae32-497a-8859-0c6fecc1a72e
-- title:
--   Cumulant, drift, and noise tensors in localization coordinates
-- statement:
--   For a compactly supported probability measure $\mu$ on $\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}n)$ and localization parameter $p$, `energyTensor`, `lowerTensor`, and `noiseTensor` are coordinate-indexed tensors built from posterior cumulants and the lower drift, after applying the inverse square root of the covariance to Euclidean basis vectors. The noise tensor has one additional distinguished coordinate $k\in\operatorname{Fin}n$ and uses a cumulant of order $r+2$. `conjugatedNoiseOperator` is the covariance-conjugated derivative of the noise operator, and `sandwich P` is the continuous linear map sending an operator $Q$ to $P\circ Q\circ P$.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
--   import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Conjugation
--   import FunctionalInequalities.KLS.BKL.Localization.NoiseBound
--   import FunctionalInequalities.Probability.Diffusion.VectorGenerator
--   import FunctionalInequalities.Analysis.Tensor.EnergyForm
--   import FunctionalInequalities.KLS.BKL.Localization.Standardization
--   import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
--   import FunctionalInequalities.KLS.BKL.Posterior.Covariance
--   import FunctionalInequalities.Probability.Diffusion.Generator
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def energyTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
--       (Fin r → Fin n) → ℝ :=
--     fun K => cumulant
--       (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
--       (Fin.cons u fun s =>
--         inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Localization/CumulantGenerator`](https://prove2.me/theorems/f937fdfc-a22d-4fdf-a9aa-a094d34ecbc2), [`KLS/BKL/Localization/CovarianceGenerator`](https://prove2.me/theorems/7af1dbcb-be0a-4bda-96c4-e0b07cecb1c1), [`KLS/BKL/Localization/CumulantDerivative`](https://prove2.me/theorems/b075fb8a-3376-43d8-a3ac-d3bc2b12f9f8), [`KLS/BKL/CumulantEnergy/Conjugation`](https://prove2.me/theorems/44ac1865-c5a7-46f3-bb27-cb9b8ec7e3f5), [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72), [`Probability/Diffusion/VectorGenerator`](https://prove2.me/theorems/a27154a7-c41b-4d48-aa0c-9939263debb7), [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e), [`KLS/BKL/Localization/Standardization`](https://prove2.me/theorems/d6ac7b3b-4286-4c25-abe4-12ef241d0c20), [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Posterior/Covariance`](https://prove2.me/theorems/cf6ff972-6f6d-497d-a1ff-ea269ff919aa), [`Probability/Diffusion/Generator`](https://prove2.me/theorems/ee0b5d14-6576-4335-ba28-d45bb3683eb2).
--
--   Theorems in source order:
--
--   - [`stdMatrix_conjugatedNoiseOperator`](https://prove2.me/theorems/f3141ac7-dca0-4168-8847-cc7e72ce9ce4)
--   - [`generator_cumulantEnergy_eq`](https://prove2.me/theorems/6cd32b47-947e-4f45-b7b2-d7005d995bc0)
--   - [`generator_cumulantEnergy_ge`](https://prove2.me/theorems/d995a803-9dc2-4144-b611-6d14e68dd120)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean) · `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean#L32-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Generator`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Generator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CovarianceGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Conjugation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_VectorGenerator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Standardization
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Posterior_Covariance
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Diffusion_Generator

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor
namespace FunctionalInequalities
namespace KLS
namespace BKL
namespace Localization
variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)
def energyTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    (Fin r → Fin n) → ℝ :=
  fun K => cumulant
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
    (Fin.cons u fun s =>
      inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
def lowerTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    (Fin r → Fin n) → ℝ :=
  fun K => lowerDrift
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
    (Fin.cons u fun s =>
      inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0
def noiseTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n))
    (k : Fin n) : (Fin r → Fin n) → ℝ :=
  fun K => cumulant
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1 + 1)
    (Fin.cons u
      (Fin.snoc
        (fun s =>
          inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
        (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ k))))
def conjugatedNoiseOperator (p : Param n) (k : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  inverseSqrt (cov μ hc p) *
    fderiv ℝ (cov μ hc) p (noise μ hc p k) *
    inverseSqrt (cov μ hc p)
 def sandwich
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ((ContinuousLinearMap.compL ℝ
    (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))).flip P).comp
    (ContinuousLinearMap.compL ℝ
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) P)
end Localization
end BKL
end KLS
end FunctionalInequalities


