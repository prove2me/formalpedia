-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
-- name    : KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:31:29.920888+00:00
-- url     : https://prove2.me/theorems/a4f34702-f144-4f20-bcf3-54aeac23be7a
-- title:
--   Matrix-entry coordinates and quadratic floors
-- statement:
--   `FunctionalInequalities.Analysis.matrixEntries` views a real matrix as an element of the Euclidean space indexed by pairs of indices, using the Frobenius-coordinate representation. `QuadraticFloor A a` means that $a\sum_i v_i^2\le v\,\mathbin{\text{⬝ᵥ}}\,(A\,\mathbin{\text{*ᵥ}}\,v)$ for every coordinate vector v. The private `outer` definition forms the matrix with entries $v_i v_j$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L77-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity`; the repository is private at upload time).

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder Kronecker
namespace FunctionalInequalities
namespace Analysis
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
/-- Euclidean view of the matrix entries; its norm is the Frobenius norm. -/
def matrixEntries (A : Matrix ι ι ℝ) : EuclideanSpace ℝ (ι × ι) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)
end Frobenius
section Floor
open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
/-- A quadratic lower floor `a ‖v‖² ≤ ⟪v, A v⟫` in coordinates. -/
def QuadraticFloor (A : Matrix ι ι ℝ) (a : ℝ) : Prop :=
  ∀ v : ι → ℝ, a * (∑ i, (v i) ^ 2) ≤ v ⬝ᵥ (A *ᵥ v)
variable [DecidableEq ι]
 def outer (v : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i * v j
end Floor
end Analysis
end FunctionalInequalities


