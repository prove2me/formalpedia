-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
-- name    : OAI_Combinatorics_SecondNeighborhood_MatrixMapsPolynomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:56:21.536039+00:00
-- url     : https://prove2.me/theorems/7a027ff8-6c1a-45f7-bc0b-44dff69fad07
-- title:
--   Polynomial versions of the cover matrices $L$ and $N$
-- statement:
--   Let $r$ be a relation on a finite set $V$. Consider finite sets $R,C\subseteq V\times V$ of pairs. A pair $a\in R$ and a pair $b\in C$ conflict if $a_1\to b_1$ and $b_2\to a_2$. A pair $a\in R$ left-covers $z$ if $a_2=z_2$ and $a_1\to z_1$, and $b\in C$ right-covers $z$ if $b_1=z_1$ and $b_2\to z_2$. $Z(R,C)$ is the set of pairs $z$ that are both left-covered by some element of $R$ and right-covered by some element of $C$.
--
--   1. **$L$ with variable entries.** The $Z\times R$ matrix whose entry at $(z,\rho)$ is the variable $X_{a,(\rho_1,z_1)}$ when $\rho$ left-covers $z$ ($z_2=\rho_2$ and $\rho_1\to z_1$), and $0$ otherwise.
--   2. **$N$ with variable entries.** The $C\times Z$ matrix whose entry at $(\gamma,z)$ is $X_{b,(\gamma_2,z_2)}$ when $\gamma$ right-covers $z$, and $0$ otherwise.
--   3. **Evaluation.** Evaluating at $v$ gives the real matrices $L$ and $N$ (and $N^{\mathsf T}$) built from the selected coefficients $a_v,b_v$.
--
--   The polynomial matrices carry the generic information. Their nonzero minors correspond to matchings in the cover graph, and they specialize to concrete real coefficient matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatrixMapsPolynomial.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatrixMapsPolynomial.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open scoped Classical Matrix

variable {X : Type*} [Fintype X] [DecidableEq X]

noncomputable def matrixLPolynomial (r : X → X → Prop) (R C : Finset (X × X)) :
    Matrix ↥(Z r R C) ↥R (MvPolynomial (CoefficientVariables X) ℝ) :=
  supportedVariableMatrix
    (fun z left => z.1.2 = left.1.2 ∧ r left.1.1 z.1.1)
    (fun z left => Sum.inl (left.1.1, z.1.1))

noncomputable def matrixNPolynomial (r : X → X → Prop) (R C : Finset (X × X)) :
    Matrix ↥C ↥(Z r R C) (MvPolynomial (CoefficientVariables X) ℝ) :=
  supportedVariableMatrix
    (fun right z => right.1.1 = z.1.1 ∧ r right.1.2 z.1.2)
    (fun right z => Sum.inr (right.1.2, z.1.2))

@[simp] theorem matrixLPolynomial_apply (r : X → X → Prop)
    (R C : Finset (X × X)) (z : ↥(Z r R C)) (left : ↥R) :
    matrixLPolynomial r R C z left =
      if z.1.2 = left.1.2 ∧ r left.1.1 z.1.1
      then MvPolynomial.X (Sum.inl (left.1.1, z.1.1)) else 0 := by
  classical
  by_cases h : z.1.2 = left.1.2 ∧ r left.1.1 z.1.1 <;>
    simp [matrixLPolynomial, supportedVariableMatrix, h]

@[simp] theorem matrixNPolynomial_apply (r : X → X → Prop)
    (R C : Finset (X × X)) (right : ↥C) (z : ↥(Z r R C)) :
    matrixNPolynomial r R C right z =
      if right.1.1 = z.1.1 ∧ r right.1.2 z.1.2
      then MvPolynomial.X (Sum.inr (right.1.2, z.1.2)) else 0 := by
  classical
  by_cases h : right.1.1 = z.1.1 ∧ r right.1.2 z.1.2 <;>
    simp [matrixNPolynomial, supportedVariableMatrix, h]

@[simp] theorem eval_matrixLPolynomial (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixLPolynomial r R C) =
      matrixL r R C (selectedA r v) := by
  classical
  ext z left
  by_cases hcoord : z.1.2 = left.1.2 <;>
    by_cases harrow : r left.1.1 z.1.1 <;>
    simp [evalPolynomialMatrix_apply, matrixLPolynomial_apply, matrixL_apply,
      selectedA, hcoord, harrow]

@[simp] theorem eval_matrixNPolynomial (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNPolynomial r R C) =
      matrixN r R C (selectedB r v) := by
  classical
  ext right z
  by_cases hcoord : right.1.1 = z.1.1 <;>
    by_cases harrow : r right.1.2 z.1.2 <;>
    simp [evalPolynomialMatrix_apply, matrixNPolynomial_apply, matrixN_apply,
      selectedB, hcoord, harrow]

@[simp] theorem eval_matrixNPolynomial_transpose (r : X → X → Prop)
    (R C : Finset (X × X)) (v : CoefficientVariables X → ℝ) :
    evalPolynomialMatrix v (matrixNPolynomial r R C)ᵀ =
      (matrixN r R C (selectedB r v))ᵀ := by
  have h := eval_matrixNPolynomial r R C v
  ext z right
  exact congrFun (congrFun h right) z

end SeymourSecondNeighborhood.Pruning

end OAI


