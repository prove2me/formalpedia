-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:24:35.838914+00:00
-- url     : https://prove2.me/theorems/78ef3e3d-95aa-4132-ae15-5c8d71915799
-- title:
--   Coordinate matrix of a continuous linear operator
-- statement:
--   For a continuous linear operator $L : \mathbb{R}^n \to \mathbb{R}^n$, `n10_matrix L` is the real matrix whose $(r,s)$ entry is the inner product of $L(e_r)$ with the standard basis vector $e_s$ of `EuclideanSpace ℝ (Fin n)`. It is a private coordinate representation used by the weak-Hessian development.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.HessianOperator
--   import FunctionalInequalities.Analysis.WeakDerivative.Calculus
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def n10_matrix {n : ℕ}
--       (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
--       Matrix (Fin n) (Fin n) ℝ :=
--     fun r s =>
--       (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
--         (L (EuclideanSpace.basisFun (Fin n) ℝ r))
--         (EuclideanSpace.basisFun (Fin n) ℝ s)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Theorems in source order:
--
--   - [`ae_weak_third_derivative_symm`](https://prove2.me/theorems/236baf49-0092-428b-8c19-9934eff0cfd3)
--   - [`norm_hessianMatrix_entry_le_of_lipschitz_gradient`](https://prove2.me/theorems/c390fe75-eaf1-41ee-934b-fddb8427fab6)
--   - [`memLp_cutoff_mul_hessianMatrix_entry`](https://prove2.me/theorems/a87ed401-510c-4f6e-8e89-854801032ee1)
--   - [`chain_coordinate_of_differentiableAt_gradient`](https://prove2.me/theorems/5a18cc05-1ac8-4293-a020-60dea2d6f206)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean) · `FunctionalInequalities.Analysis.BakryEmery.WeakHessian` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean#L352-L358 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.WeakHessian`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_WeakHessian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
noncomputable section HessianEntryBounds
open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Stein
 def n10_matrix {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r s =>
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (L (EuclideanSpace.basisFun (Fin n) ℝ r))
      (EuclideanSpace.basisFun (Fin n) ℝ s)
end Stein
end Probability
end FunctionalInequalities
end HessianEntryBounds


