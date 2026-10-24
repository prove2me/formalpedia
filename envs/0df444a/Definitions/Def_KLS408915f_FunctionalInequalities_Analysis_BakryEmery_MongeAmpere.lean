-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:46:49.777678+00:00
-- url     : https://prove2.me/theorems/fadcf3b7-5e4d-4090-8aa4-17a11135b430
-- title:
--   Hessian matrix in an orthonormal basis
-- statement:
--   For a finite-dimensional real inner-product space $E$, a function $\varphi : E \to \mathbb{R}$, an orthonormal basis $b$ indexed by `Fin m`, and $x \in E$, `hessianMatrixIn φ b x` is the matrix with entries $D^2\varphi(x)(b_i,b_j)$. The module also contains supporting infrastructure for the Monge–Ampère log-determinant identities and positivity statements described in its header, but the listed declaration is this Hessian-coordinate definition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean#L39-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
/-- The Hessian matrix `(D²φ(x)(b i, b j))_{ij}` of `φ` in an orthonormal basis `b`. -/
def hessianMatrixIn {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E) (x : E) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)
end BakryEmery
end Analysis
end FunctionalInequalities


