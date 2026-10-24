-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
-- name    : KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:32:16.190024+00:00
-- url     : https://prove2.me/theorems/2f6706ea-78f2-46ab-814d-e36ee91ca482
-- title:
--   Basis-defined principal inverse square roots
-- statement:
--   `inverseSqrtIn b A` pulls back the canonical continuous-functional-calculus square root of the inverse matrix of $A$ in the orthonormal basis $b$. `inverseSqrt A` uses the standard orthonormal basis of the finite-dimensional real inner-product space; these declarations define the operators but do not themselves state the positivity, inverse, uniqueness, or basis-independence properties described in the module documentation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean#L30-L109 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.InverseSqrt`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Operator_InverseSqrt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The principal (positive) inverse square root of `A` computed in the orthonormal basis `b`: the canonical
matrix `CFC.sqrt` of `(operatorMatrix b A)⁻¹`, pulled back to an operator. -/
def inverseSqrtIn (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  operatorOfMatrix b (CFC.sqrt ((operatorMatrix b A)⁻¹))
/-- The principal inverse square root `A^{-1/2}` (in the standard orthonormal basis; basis independent for
positive units). -/
def inverseSqrt (A : E →L[ℝ] E) : E →L[ℝ] E :=
  inverseSqrtIn (stdOrthonormalBasis ℝ E) A
end Analysis
end FunctionalInequalities


