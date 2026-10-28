-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:20:15.483751+00:00
-- url     : https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392
-- title:
--   Hessian operators and coordinate matrices
-- statement:
--   `hessianOperator φ x` is the continuous linear operator $D(\nabla\phi)(x):E\to E$. For $\phi$ on `EuclideanSpace ℝ (Fin n)`, `Probability.Stein.hessianMatrix` is the matrix whose $(i,j)$ entry is the bilinear second derivative $D^2\phi(y)[e_i,e_j]$ in the standard coordinate basis. These definitions provide operator and coordinate representations of the Hessian.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Calculus
--   import FunctionalInequalities.Analysis.Operator.Coordinates
--   import FunctionalInequalities.Analysis.Cutoff.Profile
--   import Mathlib.LinearAlgebra.FiniteDimensional.Basic
--   import Mathlib.Analysis.InnerProductSpace.Adjoint
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def hessianOperator (φ : E → ℝ) (x : E) : E →L[ℝ] E := fderiv ℝ (gradient φ) x
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Calculus`](https://prove2.me/theorems/aff8478c-96df-49c0-bd72-24bb70d5d99a), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788), [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/HessianOperator.lean) · `FunctionalInequalities.Analysis.BakryEmery.HessianOperator` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/HessianOperator.lean#L46-L557 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_HessianOperator`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The Hessian operator `∇²φ(x) = D(∇φ)(x) : E →L[ℝ] E`. The Euclidean coordinate object
`Probability.Stein.hessianMatrix` is its standard-basis entry matrix (`Probability.Stein.hessianMatrix_eq_operatorEntry_hessianOperator`). -/
def hessianOperator (φ : E → ℝ) (x : E) : E →L[ℝ] E := fderiv ℝ (gradient φ) x
end BakryEmery
end Analysis
end FunctionalInequalities
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Probability
namespace Stein
/-- The Hessian matrix `(∇²φ)_{ij}(y) = D²φ(y)(e_i, e_j)` of `φ` in the standard basis. -/
noncomputable def hessianMatrix {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : Probability.Stein.KernelMatrix n :=
  fun i j => bilinearIteratedFDerivTwo ℝ φ y (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
end Stein
end Probability
end FunctionalInequalities


