-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
-- name    : KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:31:50.095534+00:00
-- url     : https://prove2.me/theorems/8f9dcf00-04bd-402b-ae9f-7c470913198a
-- title:
--   Orthonormal coordinates for continuous linear operators
-- statement:
--   `operatorEntry` is the coordinate $\langle b_i,Mb_j\rangle$ of a continuous operator M in an orthonormal basis b. `operatorMatrix` and `operatorOfMatrix` convert between operators and matrices in that basis, while `operatorMatrixL` and `operatorOfMatrixL` provide continuous linear maps between operators and Euclidean matrix-entry coordinates. The bundle also proves the displayed coordinate identities and defines `Probability.Stein.KernelMatrix n` as the real matrix type indexed by `Fin n`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean#L27-L267 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.Coordinates`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped RealInnerProductSpace MatrixOrder
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The `(i, j)` entry `⟪b i, M (b j)⟫` of an operator in an orthonormal basis. -/
def operatorEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (M : E →L[ℝ] E) (i j : Fin m) : ℝ :=
  ⟪b i, M (b j)⟫
section OperatorMatrix
open Matrix
variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The matrix of an operator in an orthonormal basis (`LinearMap.toMatrixOrthonormal`); its `(i, j)` entry is
`operatorEntry b T i j` (`operatorMatrix_apply_eq_operatorEntry`). -/
def operatorMatrix (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) : Matrix ι ι ℝ :=
  LinearMap.toMatrixOrthonormal b T.toLinearMap
/-- The operator with a given matrix in an orthonormal basis (inverse of `operatorMatrix`). -/
def operatorOfMatrix (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) : E →L[ℝ] E :=
  ((LinearMap.toMatrixOrthonormal b).symm M).toContinuousLinearMap
 def matrixEntriesLinear : Matrix ι ι ℝ →ₗ[ℝ] EuclideanSpace ℝ (ι × ι) where
  toFun := matrixEntries
  map_add' A B := by ext ij; rfl
  map_smul' a A := by ext ij; rfl
 def matrixOfEntriesLinear : EuclideanSpace ℝ (ι × ι) →ₗ[ℝ] Matrix ι ι ℝ where
  toFun z i j := z (i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- The operator with given Euclidean matrix entries, as a continuous linear map (finite-dimensional
continuity gives a norm comparison between Frobenius entries and the operator norm; no isometry is
asserted). -/
def operatorOfMatrixL (b : OrthonormalBasis ι ℝ E) :
    EuclideanSpace ℝ (ι × ι) →L[ℝ] (E →L[ℝ] E) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp
    ((LinearMap.toMatrixOrthonormal b).symm.toAlgEquiv.toLinearMap.comp
      FunctionalInequalities.Analysis.matrixOfEntriesLinear)).toContinuousLinearMap
@[simp] theorem operatorOfMatrixL_matrixEntries (b : OrthonormalBasis ι ℝ E) (M : Matrix ι ι ℝ) :
    operatorOfMatrixL b (matrixEntries M) = operatorOfMatrix b M := rfl
/-- The Euclidean matrix entries of an operator, as a continuous linear map. -/
def operatorMatrixL (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →L[ℝ] EuclideanSpace ℝ (ι × ι) :=
  (FunctionalInequalities.Analysis.matrixEntriesLinear.comp ((LinearMap.toMatrixOrthonormal b).toAlgEquiv.toLinearMap.comp
    LinearMap.toContinuousLinearMap.symm.toLinearMap)).toContinuousLinearMap
@[simp] theorem operatorMatrixL_apply (b : OrthonormalBasis ι ℝ E) (T : E →L[ℝ] E) :
    operatorMatrixL b T = matrixEntries (operatorMatrix b T) := rfl
end OperatorMatrix
end Analysis
end FunctionalInequalities
namespace FunctionalInequalities
namespace Probability
namespace Stein
abbrev KernelMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
end Stein
end Probability
end FunctionalInequalities


