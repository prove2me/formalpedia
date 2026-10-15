-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
-- name    : OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:42:34.295098+00:00
-- url     : https://prove2.me/theorems/1c516af8-7a83-49d1-a480-adcdb691729b
-- title:
--   Diagonal sign matrices and coordinate multiplication operators on the Boolean cube
-- statement:
--   Let $Q_n=\{-1,1\}^n$ be the Boolean cube and consider complex-valued functions on $Q_n$, with the point-mass basis $(e_x)_{x\in Q_n}$ and the counting inner product $\langle f,g\rangle=\sum_{x\in Q_n}\overline{f(x)}\,g(x)$. All matrices below are indexed by $Q_n\times Q_n$.
--
--   1. **Sign matrix of a real function.** For $h:Q_n\to\mathbb{R}$, $D_h$ is the diagonal matrix with entries $D_h(x,y)=h(x)$ if $x=y$ and $0$ otherwise; it is the matrix of $f\mapsto hf$ in the point-mass basis.
--
--   2. **Coordinate sign matrix.** For a coordinate $i$, $Z_i=D_{h_i}$ with $h_i(x)=x_i$, so that $(Z_if)(x)=x_i\,f(x)$.
--
--   3. **Multiplication operators.** The same diagonal maps regarded as operators on the Hilbert space $\ell^2(Q_n)$ with the counting inner product: $(M_hf)(x)=h(x)f(x)$, and its special case for $h=h_i$, multiplication by the coordinate $x_i$.
--
--   The module records their basic properties. $D_h$ is Hermitian for every real $h$. If $h$ takes only the values $\pm1$, then $D_h^2=I$, $D_h^{*}D_h=I$, the squared Hilbert–Schmidt norm $\sum_{x,y}|D_h(x,y)|^2$ equals $2^n$, $M_h^2=I$, and $\|M_hf\|=\|f\|$ for every $f$. In particular
--   $$
--   Z_i^{*}=Z_i,\qquad Z_i^{2}=I,\qquad \sum_{x,y\in Q_n}|Z_i(x,y)|^2=2^n .
--   $$
--
--   The coordinate multipliers link the operator side of the Gotsman–Linial argument to the edge structure of the cube: multiplication by $x_i$ sends $\chi_S$ to $\chi_{S\triangle\{i\}}$ and hence maps functions of Fourier degree at most $k$ to functions of degree at most $k+1$, and commutators with the $Z_i$ measure Hamming distances between the row and column indices of a matrix.
--
--   **Formalization Note** Vertices are Boolean functions on `Fin n`, read as signs ($\mathtt{true}\mapsto1$, $\mathtt{false}\mapsto-1$) via `cubeCoord`. The matrices are `signMatrix` and `coordinateSignMatrix`; the operators are `signMultiplier` and `coordinateMultiplier`, obtained with `Matrix.toEuclideanCLM` on `EuclideanSpace` over the cube, so operator norms refer to the Euclidean (counting) norm. The Hilbert–Schmidt quantity is the explicit entry sum `hsNormSq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/CoordinateMultipliers.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/CoordinateMultipliers.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator

namespace OAI

/-!
# Actual diagonal sign and coordinate operators on the cube

The matrices here act on the cube with its counting inner product.  Their
continuous linear maps act on `EuclideanSpace`, so all operator-norm statements
refer to the intended Euclidean norm.  The Hilbert--Schmidt statements use the
explicit squared-entry sum `hsNormSq`.
-/

noncomputable section

open scoped BigOperators Matrix

namespace LeanBlast.GotsmanLinial

variable {n : ℕ}

/-- Multiplication by a real function on the cube, represented in the point-mass basis. -/
def signMatrix (h : Cube n → ℝ) : Matrix (Cube n) (Cube n) ℂ :=
  Matrix.diagonal (fun x => (h x : ℂ))

/-- The actual cube coordinate-sign matrix `Z_i`. -/
def coordinateSignMatrix (i : Fin n) : Matrix (Cube n) (Cube n) ℂ :=
  signMatrix (fun x => cubeCoord x i)

@[simp] theorem signMatrix_apply (h : Cube n → ℝ) (x y : Cube n) :
    signMatrix h x y = if x = y then (h x : ℂ) else 0 := by
  simp [signMatrix, Matrix.diagonal_apply]

@[simp] theorem signMatrix_apply_self (h : Cube n → ℝ) (x : Cube n) :
    signMatrix h x x = (h x : ℂ) := by simp

@[simp] theorem coordinateSignMatrix_apply (i : Fin n) (x y : Cube n) :
    coordinateSignMatrix i x y = if x = y then (cubeCoord x i : ℂ) else 0 :=
  signMatrix_apply _ x y

@[simp] theorem signMatrix_conjTranspose (h : Cube n → ℝ) :
    (signMatrix h).conjTranspose = signMatrix h := by
  simp [signMatrix, Matrix.diagonal_conjTranspose]

@[simp] theorem signMatrix_star (h : Cube n → ℝ) :
    star (signMatrix h) = signMatrix h :=
  signMatrix_conjTranspose h

/-- A sign-valued real diagonal is an involution. -/
theorem signMatrix_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMatrix h * signMatrix h = 1 := by
  classical
  rw [signMatrix, Matrix.diagonal_mul_diagonal]
  have hs : (fun x => (h x : ℂ) * (h x : ℂ)) = fun _ : Cube n => (1 : ℂ) := by
    funext x
    rcases hh x with hx | hx <;> simp [hx]
  rw [hs, Matrix.diagonal_one]

theorem signMatrix_conjTranspose_mul (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) :
    (signMatrix h).conjTranspose * signMatrix h = 1 := by
  rw [signMatrix_conjTranspose, signMatrix_mul_self h hh]

@[simp] theorem signMatrix_mulVec (h : Cube n → ℝ) (v : Cube n → ℂ) (x : Cube n) :
    (signMatrix h *ᵥ v) x = (h x : ℂ) * v x := by
  simp [signMatrix, Matrix.mulVec_diagonal]

theorem hsNormSq_signMatrix (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : hsNormSq (signMatrix h) = (2 : ℝ) ^ n := by
  rw [hsNormSq_of_unitary _ (signMatrix_conjTranspose_mul h hh), card_cube]
  simp

@[simp] theorem coordinateSignMatrix_conjTranspose (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose = coordinateSignMatrix i :=
  signMatrix_conjTranspose _

@[simp] theorem coordinateSignMatrix_star (i : Fin n) :
    star (coordinateSignMatrix i) = coordinateSignMatrix i :=
  signMatrix_star _

@[simp] theorem coordinateSignMatrix_mul_self (i : Fin n) :
    coordinateSignMatrix i * coordinateSignMatrix i = 1 :=
  signMatrix_mul_self _ (fun x => cubeCoord_cases x i)

@[simp] theorem coordinateSignMatrix_conjTranspose_mul (i : Fin n) :
    (coordinateSignMatrix i).conjTranspose * coordinateSignMatrix i = 1 := by simp

@[simp] theorem coordinateSignMatrix_mul_conjTranspose (i : Fin n) :
    coordinateSignMatrix i * (coordinateSignMatrix i).conjTranspose = 1 := by simp

@[simp] theorem coordinateSignMatrix_mulVec (i : Fin n) (v : Cube n → ℂ) (x : Cube n) :
    (coordinateSignMatrix i *ᵥ v) x = (cubeCoord x i : ℂ) * v x :=
  signMatrix_mulVec _ v x

@[simp] theorem hsNormSq_coordinateSignMatrix (i : Fin n) :
    hsNormSq (coordinateSignMatrix i) = (2 : ℝ) ^ n :=
  hsNormSq_signMatrix _ (fun x => cubeCoord_cases x i)

/-- The same diagonal action on the counting-inner-product Euclidean space. -/
def signMultiplier (h : Cube n → ℝ) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h)

/-- The actual coordinate multiplier on Euclidean space. -/
def coordinateMultiplier (i : Fin n) :
    EuclideanSpace ℂ (Cube n) →L[ℂ] EuclideanSpace ℂ (Cube n) :=
  signMultiplier (fun x => cubeCoord x i)

@[simp] theorem toEuclideanCLM_signMatrix (h : Cube n → ℝ) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = signMultiplier h := rfl

@[simp] theorem toEuclideanCLM_coordinateSignMatrix (i : Fin n) :
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (coordinateSignMatrix i) =
      coordinateMultiplier i := rfl

@[simp] theorem signMultiplier_apply (h : Cube n → ℝ)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    signMultiplier h v x = (h x : ℂ) * v x := by
  change (signMatrix h *ᵥ fun y => v y) x = _
  exact signMatrix_mulVec h _ x

@[simp] theorem coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) (x : Cube n) :
    coordinateMultiplier i v x = (cubeCoord x i : ℂ) * v x :=
  signMultiplier_apply _ v x

theorem signMultiplier_mul_self (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) : signMultiplier h * signMultiplier h = 1 := by
  change Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) *
    Matrix.toEuclideanCLM (n := Cube n) (𝕜 := ℂ) (signMatrix h) = 1
  rw [← map_mul, signMatrix_mul_self h hh, map_one]

@[simp] theorem coordinateMultiplier_mul_self (i : Fin n) :
    coordinateMultiplier i * coordinateMultiplier i = 1 :=
  signMultiplier_mul_self _ (fun x => cubeCoord_cases x i)

theorem norm_signMultiplier_apply (h : Cube n → ℝ)
    (hh : ∀ x, h x = 1 ∨ h x = -1) (v : EuclideanSpace ℂ (Cube n)) :
    ‖signMultiplier h v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  rcases hh x with hx | hx <;> simp [signMultiplier_apply, hx]

@[simp] theorem norm_coordinateMultiplier_apply (i : Fin n)
    (v : EuclideanSpace ℂ (Cube n)) : ‖coordinateMultiplier i v‖ = ‖v‖ :=
  norm_signMultiplier_apply _ (fun x => cubeCoord_cases x i) v

end LeanBlast.GotsmanLinial

end

end OAI


