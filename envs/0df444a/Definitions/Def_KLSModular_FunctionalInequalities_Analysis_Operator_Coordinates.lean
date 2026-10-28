-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
-- name    : KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:22:02.349185+00:00
-- url     : https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788
-- title:
--   Orthonormal coordinates for continuous linear operators
-- statement:
--   `operatorEntry` is the coordinate $\langle b_i,Mb_j\rangle$ of a continuous operator M in an orthonormal basis b. `operatorMatrix` and `operatorOfMatrix` convert between operators and matrices in that basis, while `operatorMatrixL` and `operatorOfMatrixL` provide continuous linear maps between operators and Euclidean matrix-entry coordinates. The bundle also proves the displayed coordinate identities and defines `Probability.Stein.KernelMatrix n` as the real matrix type indexed by `Fin n`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.RingInverseDerivative
--   import FunctionalInequalities.Analysis.Matrix.Positivity
--   import Mathlib.Analysis.Normed.Operator.Banach
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import Mathlib.Analysis.Matrix.Order
--   import Mathlib.Analysis.InnerProductSpace.Positive
--   import Mathlib.Analysis.Normed.Module.FiniteDimension
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def operatorEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E) (M : E →L[ℝ] E) (i j : Fin m) : ℝ :=
--     ⟪b i, M (b j)⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/RingInverseDerivative`](https://prove2.me/theorems/c96c8529-32d0-4d4a-bf8d-245101c7e97a), [`Analysis/Matrix/Positivity`](https://prove2.me/theorems/ed2fd089-dbff-4fcc-9c49-b75c2c3c268c).
--
--   Theorems in source order:
--
--   - [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean) · `FunctionalInequalities.Analysis.Operator.Coordinates` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean#L27-L267 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Operator.Coordinates`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Operator_Coordinates`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_RingInverseDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Module.FiniteDimension

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


