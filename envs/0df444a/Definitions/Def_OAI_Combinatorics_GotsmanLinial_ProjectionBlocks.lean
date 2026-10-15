-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
-- name    : OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:40:02.334144+00:00
-- url     : https://prove2.me/theorems/77c3037c-6ac4-4be4-9f30-97bc237e5592
-- title:
--   Orthogonal projection families, spectral gradings, and matrices of operators in an orthonormal basis
-- statement:
--   This module fixes the linear-algebraic vocabulary for splitting a complex matrix into blocks along a finite orthogonal decomposition of the identity, and for passing between operators on a finite-dimensional Hilbert space and their matrices. Throughout, $\iota$ and $K$ are finite index sets and matrices are square matrices in $\mathbb{C}^{\iota\times\iota}$.
--
--   1. **Orthogonal projection family.** A family $(P_k)_{k\in K}$ in $\mathbb{C}^{\iota\times\iota}$ is an orthogonal projection family if each $P_k$ is Hermitian ($P_k^{*}=P_k$) and idempotent ($P_k^2=P_k$), distinct members annihilate each other ($P_rP_s=0$ for $r\neq s$), and
--   $$
--   \sum_{k\in K}P_k=I .
--   $$
--   Equivalently, $\mathbb{C}^{\iota}$ is the orthogonal direct sum of the ranges of the $P_k$.
--
--   2. **Grading by a real weight.** For a family $(P_k)_{k\in K}$ and a weight $\omega:K\to\mathbb{R}$, the grading matrix is $G_\omega=\sum_{k\in K}\omega(k)\,P_k$. For an orthogonal projection family, $G_\omega$ is the Hermitian matrix that acts as the scalar $\omega(k)$ on the range of $P_k$.
--
--   3. **Degree and centered gradings.** For a family $(P_k)_{k=0}^{n}$ indexed by $\{0,1,\dots,n\}$, the degree grading is $N=\sum_{k=0}^{n}k\,P_k$ and the centered grading is $\sum_{k=0}^{n}\bigl(k-\tfrac n2\bigr)P_k$, which equals $N-\tfrac n2 I$ when the family sums to the identity.
--
--   4. **Matrix of an operator.** Let $E$ be a finite-dimensional complex inner product space with an orthonormal basis $b=(b_i)_{i\in\iota}$. A linear operator $T:E\to E$ has the matrix $[T]_b\in\mathbb{C}^{\iota\times\iota}$ with entries $[T]_b(i,j)=\langle b_i,\,T b_j\rangle$, and $T\mapsto[T]_b$ is an isomorphism of complex algebras from the operators on $E$ onto $\mathbb{C}^{\iota\times\iota}$. In particular it preserves $0$, the identity, sums, differences, products, scalar multiples and finite sums, and for $E=\mathbb{C}^{\iota}$ with its standard basis the matrix of $v\mapsto Av$ is $A$ itself.
--
--   These notions allow orthogonal projections constructed abstractly in a Hilbert space to be handled as explicit matrices, where blocks $P_sAP_r$ and commutators with gradings can be computed entrywise. In the Gotsman–Linial argument the family $(P_k)_{k=0}^n$ is a weighted degree grading of functions on the Boolean cube $\{-1,1\}^n$.
--
--   **Formalization Note** The family property is the `Prop`-valued structure `OrthogonalProjectionFamily`; the gradings are `matrixGrading`, `degreeGrading` and `centeredGrading`, with the real weights cast to complex numbers. The operator–matrix correspondence is `operatorMatrixEquiv` (an algebra equivalence built from Mathlib's `LinearMap.toMatrixOrthonormal`, for continuous linear operators) and `operatorMatrix`; the accompanying simp lemmas record its compatibility with the algebra operations and with `Matrix.toEuclideanCLM`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/ProjectionBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/ProjectionBlocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt

namespace OAI

/-!
# Matrix blocks of a finite orthogonal projection family

The Hilbert--Schmidt quantity below is the explicit sum of squared entry norms
rather than an ambient matrix norm instance.
-/

open scoped BigOperators ComplexConjugate
open Module

noncomputable section

namespace LeanBlast.GotsmanLinial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- A finite orthogonal decomposition of the identity by Hermitian projections. -/
structure OrthogonalProjectionFamily (P : κ → Matrix ι ι ℂ) : Prop where
  selfAdjoint : ∀ k, IsSelfAdjoint (P k)
  idempotent : ∀ k, P k * P k = P k
  orthogonal : ∀ r s, r ≠ s → P r * P s = 0
  sum_eq_one : ∑ k, P k = 1

namespace OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ} (hP : OrthogonalProjectionFamily P)

include hP

end OrthogonalProjectionFamily

variable {P : κ → Matrix ι ι ℂ}

/-- The real-valued spectral multiplier defined by the projection family. -/
def matrixGrading (P : κ → Matrix ι ι ℂ) (weight : κ → ℝ) : Matrix ι ι ℂ :=
  ∑ k, (weight k : ℂ) • P k

/-- The degree grading associated to projections indexed from zero to `n`. -/
def degreeGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ)

/-- The degree grading centered at `n / 2`. -/
def centeredGrading {n : ℕ} (P : Fin (n + 1) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  matrixGrading P fun k => (k.val : ℝ) - (n : ℝ) / 2

section OperatorTransport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance instCompleteSpace_oAI : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Matrix representation of a continuous operator in an orthonormal basis,
bundled with its algebraic compatibility. -/
def operatorMatrixEquiv (b : OrthonormalBasis ι ℂ E) :
    (E →L[ℂ] E) ≃ₐ[ℂ] Matrix ι ι ℂ :=
  (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm.trans
    (LinearMap.toMatrixOrthonormal b).toAlgEquiv

/-- Matrix entries for the counting orthonormal basis or any chosen
orthonormal basis. -/
def operatorMatrix (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) : Matrix ι ι ℂ :=
  operatorMatrixEquiv b T

@[simp]
theorem operatorMatrix_zero (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (0 : E →L[ℂ] E) = 0 := map_zero (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_one (b : OrthonormalBasis ι ℂ E) :
    operatorMatrix b (1 : E →L[ℂ] E) = 1 := map_one (operatorMatrixEquiv b)

@[simp]
theorem operatorMatrix_add (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A + B) = operatorMatrix b A + operatorMatrix b B :=
  map_add (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_sub (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A - B) = operatorMatrix b A - operatorMatrix b B :=
  map_sub (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_mul (b : OrthonormalBasis ι ℂ E) (A B : E →L[ℂ] E) :
    operatorMatrix b (A * B) = operatorMatrix b A * operatorMatrix b B :=
  map_mul (operatorMatrixEquiv b) A B

@[simp]
theorem operatorMatrix_smul (b : OrthonormalBasis ι ℂ E) (z : ℂ) (T : E →L[ℂ] E) :
    operatorMatrix b (z • T) = z • operatorMatrix b T :=
  (operatorMatrixEquiv b).toLinearEquiv.map_smul z T

@[simp]
theorem operatorMatrix_sum (b : OrthonormalBasis ι ℂ E) (T : κ → E →L[ℂ] E) :
    operatorMatrix b (∑ k, T k) = ∑ k, operatorMatrix b (T k) :=
  map_sum (operatorMatrixEquiv b) T Finset.univ

end OperatorTransport

/-- The standard-basis matrix representation is inverse to the standard
Euclidean continuous linear operator associated to a matrix. -/
@[simp]
theorem operatorMatrix_toEuclideanCLM (A : Matrix ι ι ℂ) :
    operatorMatrix (EuclideanSpace.basisFun ι ℂ)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) = A :=
  (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun ι ℂ)).apply_symm_apply A

end LeanBlast.GotsmanLinial

end

end OAI


