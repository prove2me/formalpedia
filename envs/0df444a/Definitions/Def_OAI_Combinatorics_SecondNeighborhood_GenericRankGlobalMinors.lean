-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
-- name    : OAI_Combinatorics_SecondNeighborhood_GenericRankGlobalMinors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:57:32.283187+00:00
-- url     : https://prove2.me/theorems/3c99defb-33c7-4149-b428-3a0fca0ad98c
-- title:
--   Supports of the cover matrices and their matching minors
-- statement:
--   Let $r$ be a relation on a finite set $V$. Consider finite sets $R,C\subseteq V\times V$ of pairs. A pair $a\in R$ and a pair $b\in C$ conflict if $a_1\to b_1$ and $b_2\to a_2$. A pair $a\in R$ left-covers $z$ if $a_2=z_2$ and $a_1\to z_1$, and $b\in C$ right-covers $z$ if $b_1=z_1$ and $b_2\to z_2$. $Z(R,C)$ is the set of pairs $z$ that are both left-covered by some element of $R$ and right-covered by some element of $C$.
--
--   1. **Supports.** The support of $L$ at $(z,\rho)$ is the left-cover relation: $z_2=\rho_2$ and $\rho_1\to z_1$. The support of $N^{\mathsf T}$ at $(z,\gamma)$ is the right-cover relation.
--   2. **Matching minors.** For a set $M$ of support positions, the square submatrix of the polynomial $L$, respectively $N^{\mathsf T}$, with rows and columns indexed by the edges of $M$ via their two endpoints.
--   3. **Evaluation.** These minors evaluated at $v$ are the corresponding submatrices of the real matrices built from the selected coefficients.
--
--   For a matching $M$ in the support, the determinant of its minor is a nonzero polynomial; this is proved in the source module. Hence a generic evaluation has full rank on $M$, which turns matching sizes into rank lower bounds for the real cover matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRankGlobalMinors.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankGlobalMinors.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelRestriction
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MaxSupportKernel
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_KernelConflict
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankCoefficients
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

def matrixLSupport (r : X → X → Prop) (R C : Finset (X × X))
    (z : ↥(Z r R C)) (left : ↥R) : Prop :=
  z.val.2 = left.val.2 ∧ r left.val.1 z.val.1

def matrixNTransposeSupport (r : X → X → Prop) (R C : Finset (X × X))
    (z : ↥(Z r R C)) (right : ↥C) : Prop :=
  right.val.1 = z.val.1 ∧ r right.val.2 z.val.2

@[simp] theorem matrixLSupport_iff_leftCovers (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (left : ↥R) :
    matrixLSupport r R C z left ↔ LeftCovers r left.val z.val := by
  constructor
  · rintro ⟨hcoord, harrow⟩
    exact ⟨hcoord.symm, harrow⟩
  · rintro ⟨hcoord, harrow⟩
    exact ⟨hcoord.symm, harrow⟩

@[simp] theorem matrixNTransposeSupport_iff_rightCovers (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (right : ↥C) :
    matrixNTransposeSupport r R C z right ↔ RightCovers r right.val z.val :=
  Iff.rfl

noncomputable def matrixLMatchingMinor (r : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (↥(Z r R C) × ↥R)) :
    Matrix ↥M ↥M (MvPolynomial (CoefficientVariables X) ℝ) :=
  (matrixLPolynomial r R C).submatrix (fun e : ↥M => e.val.1) (fun e => e.val.2)

noncomputable def matrixNTransposeMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C)) :
    Matrix ↥M ↥M (MvPolynomial (CoefficientVariables X) ℝ) :=
  (matrixNPolynomial r R C)ᵀ.submatrix (fun e : ↥M => e.val.1) (fun e => e.val.2)

@[simp] theorem eval_matrixLMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥R))
    (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixLMatchingMinor r R C M) =
      (matrixL r R C (selectedA r v)).submatrix
        (fun e : ↥M => e.val.1) (fun e => e.val.2) := by
  rw [matrixLMatchingMinor, evalPolynomialMatrix_submatrix, eval_matrixLPolynomial]

@[simp] theorem eval_matrixNTransposeMatchingMinor (r : X → X → Prop)
    (R C : Finset (X × X)) (M : Finset (↥(Z r R C) × ↥C))
    (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNTransposeMatchingMinor r R C M) =
      (matrixN r R C (selectedB r v))ᵀ.submatrix
        (fun e : ↥M => e.val.1) (fun e => e.val.2) := by
  rw [matrixNTransposeMatchingMinor, evalPolynomialMatrix_submatrix,
    eval_matrixNPolynomial_transpose]

end SeymourSecondNeighborhood.Pruning

end OAI


