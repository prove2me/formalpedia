-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:46:16.447862+00:00
-- url     : https://prove2.me/theorems/1af2b57f-060d-42c6-9997-fca2d2185437
-- title:
--   Hessian operators and coordinate matrices
-- statement:
--   `hessianOperator φ x` is the continuous linear operator $D(\nabla\phi)(x):E\to E$. For $\phi$ on `EuclideanSpace ℝ (Fin n)`, `Probability.Stein.hessianMatrix` is the matrix whose $(i,j)$ entry is the bilinear second derivative $D^2\phi(y)[e_i,e_j]$ in the standard coordinate basis. These definitions provide operator and coordinate representations of the Hessian.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/HessianOperator.lean#L46-L557 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.HessianOperator`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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


