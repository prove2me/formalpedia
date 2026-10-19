-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
-- name    : OAI_Combinatorics_SecondNeighborhood_GenericRank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:49:38.267116+00:00
-- url     : https://prove2.me/theorems/5222e170-14f8-47dc-919b-5c7d292ac2b5
-- title:
--   Evaluating polynomial matrices at a point
-- statement:
--   Let $K$ be a commutative ring and $M$ an $I\times J$ matrix of multivariate polynomials over $K$ in variables $\sigma$. For a point $a\in K^\sigma$, the evaluated matrix is $M(a)_{ij}=M_{ij}(a)$. Evaluation commutes with taking submatrices, and for square $M$
--   $$
--   \det\bigl(M(a)\bigr)=(\det M)(a).
--   $$
--
--   A polynomial matrix has a nonzero minor if and only if some evaluation does, over an infinite domain. Generic ranks of polynomial matrices can therefore be realized by actual real matrices, and simultaneously for finitely many matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/GenericRank.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRank.lean by skeleton subtraction
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

namespace OAI

namespace SeymourSecondNeighborhood

open scoped BigOperators

section Evaluation

variable {σ ι K : Type*} [CommRing K] [IsDomain K] [Infinite K]

end Evaluation

section Matrices

variable {σ K I J : Type*} [CommRing K]

noncomputable def evalPolynomialMatrix (a : σ → K) (M : Matrix I J (MvPolynomial σ K)) :
    Matrix I J K :=
  M.map (MvPolynomial.eval a)

@[simp] theorem evalPolynomialMatrix_apply (a : σ → K)
    (M : Matrix I J (MvPolynomial σ K)) (i : I) (j : J) :
    evalPolynomialMatrix a M i j = MvPolynomial.eval a (M i j) := rfl

@[simp] theorem evalPolynomialMatrix_submatrix {I' J' : Type*} (a : σ → K)
    (M : Matrix I J (MvPolynomial σ K)) (r : I' → I) (c : J' → J) :
    evalPolynomialMatrix a (M.submatrix r c) =
      (evalPolynomialMatrix a M).submatrix r c := rfl

@[simp] theorem det_evalPolynomialMatrix [Fintype I] [DecidableEq I]
    (a : σ → K) (M : Matrix I I (MvPolynomial σ K)) :
    (evalPolynomialMatrix a M).det = MvPolynomial.eval a M.det :=
  ((MvPolynomial.eval a).map_det M).symm

end Matrices

section SimultaneousDeterminants

variable {σ κ K : Type*} [CommRing K] [IsDomain K] [Infinite K] [Fintype κ]
variable {I : κ → Type*} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]

end SimultaneousDeterminants

section SimultaneousRanks

variable {σ κ K : Type*} [Field K] [Infinite K] [Fintype κ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

end SimultaneousRanks

end SeymourSecondNeighborhood

end OAI


