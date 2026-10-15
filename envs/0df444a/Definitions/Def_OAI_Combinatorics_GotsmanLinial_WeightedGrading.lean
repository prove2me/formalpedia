-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_WeightedGrading
-- name    : OAI_Combinatorics_GotsmanLinial_WeightedGrading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:59:08.737906+00:00
-- url     : https://prove2.me/theorems/c97e84c2-2943-426d-abff-3a3ed624bdef
-- title:
--   Weighted orthogonal grading of the Boolean cube from the transported Walsh flag
-- statement:
--   Throughout, $E$ is a finite-dimensional inner product space over $\mathbb{K}\in\{\mathbb{R},\mathbb{C}\}$ and a flag is an arbitrary sequence $(K_k)_{k\in\mathbb{N}}$ of subspaces of $E$.
--
--   1. **Flag layers and their projections.** The $k$-th layer is $L_k=K_{k+1}\cap K_k^{\perp}$, and $Q_k$ is the orthogonal projection of $E$ onto $L_k$ (its range is exactly $L_k$). For an increasing flag these are the successive orthogonal layers produced by Gram–Schmidt orthogonalization of the flag.
--
--   2. **Multiplication by a nonvanishing function.** For a finite set $\Omega$ and $a:\Omega\to\mathbb{C}$ with $a(x)\neq0$ for all $x$, the map $f\mapsto af$ is a linear automorphism of $\mathbb{C}^{\Omega}$, with inverse $f\mapsto a^{-1}f$ (pointwise reciprocal).
--
--   3. **Square-root weight operator.** For a strictly positive weight $w:\Omega\to\mathbb{R}$, $D_w$ is the linear automorphism of $\ell^2(\Omega)$ (counting inner product) given by $(D_wf)(x)=\sqrt{w(x)}\,f(x)$, with inverse $(D_w^{-1}f)(x)=f(x)/\sqrt{w(x)}$.
--
--   4. **Transported flag.** For a linear automorphism $D$ of $E$ and a flag $(F_k)$, the transported flag is $(D F_k)_{k\in\mathbb{N}}$; it is $\{0\}$ wherever $F_k=\{0\}$ and $E$ wherever $F_k=E$.
--
--   5. **Matrices of layer projections.** For an orthonormal basis $b$ of a complex space $E$, the matrix $[Q_k]_b$ of the $k$-th layer projection.
--
--   6. **Weighted Fourier flag of the cube.** For $w:\{-1,1\}^n\to\mathbb{R}$ with $w>0$ everywhere, let $V_{\le k}$ be the span of the Walsh characters of degree at most $k$ and $W_k=D_w(V_{\le k})=\{\sqrt w\,f: f\in V_{\le k}\}$. The weighted flag is $K^w_0=\{0\}$, $K^w_{k+1}=W_k$; it reaches the whole space at stage $n+1$.
--
--   7. **Weighted projection matrices.** For $k\in\{0,1,\dots,n\}$, $P^w_k$ is the matrix, in the point-mass basis of $\ell^2(\{-1,1\}^n)$, of the orthogonal projection onto the layer $K^w_{k+1}\cap(K^w_k)^{\perp}$:
--   $$
--   P^w_k=\bigl[\operatorname{proj}_{\,W_k\cap W_{k-1}^{\perp}}\bigr],\qquad W_{-1}=\{0\}.
--   $$
--
--   Since $\langle \sqrt w f,\sqrt w g\rangle=\sum_x w(x)\overline{f(x)}g(x)$, the layers correspond under $D_w$ to the degree decomposition of the weighted space $\ell^2(w)$. The matrices $(P^w_k)_{k=0}^n$ form an orthogonal decomposition of the identity whose $k$-th projection has rank $\binom nk$; they serve as the degree grading of the Gotsman–Linial argument, with the weight $w=|p|$ given by a polynomial $p$ that does not vanish on the cube.
--
--   **Formalization Note** The objects are `flagLayer`, `flagProjection` (via Mathlib's `starProjection`), `coordinateMulEquiv`, `sqrtWeightEquiv`, `transportFlag`, `flagProjectionMatrix`, `weightedFourierSpace`, `weightedFourierFlag` and `weightedProjectionMatrix`. The positivity of $w$ is passed as an explicit proof argument, and flag layers are defined for any sequence of subspaces, without a monotonicity hypothesis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/WeightedGrading.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/WeightedGrading.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions

namespace OAI

/-!
# The actual weighted orthogonal grading of the cube

The construction first orthogonalizes an arbitrary finite flag of subspaces.
It then transports the concrete Walsh flag by the invertible square-root
weight and takes the orthogonal projections in the counting Hilbert space.
The resulting matrices are proved to form an orthogonal decomposition of
the identity with the prescribed binomial multiplicities.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

section FiniteFlag

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance instCompleteSpace_oAI_1 : CompleteSpace E := FiniteDimensional.complete 𝕜 E

/-- The new orthogonal layer appearing between two consecutive stages of a flag. -/
def flagLayer (K : ℕ → Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  K (k + 1) ⊓ (K k)ᗮ

/-- The actual orthogonal projection onto a layer of a finite-dimensional flag. -/
def flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) : E →L[𝕜] E :=
  (flagLayer K k).starProjection

@[simp]
theorem range_flagProjection (K : ℕ → Submodule 𝕜 E) (k : ℕ) :
    (flagProjection K k).range = flagLayer K k :=
  Submodule.range_starProjection (flagLayer K k)

end FiniteFlag

section InvertibleWeights

variable {Ω : Type*} [Fintype Ω]

/-- Multiplication by pointwise nonzero coefficients is a linear equivalence. -/
def coordinateMulEquiv (a : Ω → ℂ) (ha : ∀ x, a x ≠ 0) :
    (Ω → ℂ) ≃ₗ[ℂ] (Ω → ℂ) where
  toFun f x := a x * f x
  invFun f x := (a x)⁻¹ * f x
  left_inv f := by
    funext x
    simp only [← mul_assoc, inv_mul_cancel₀ (ha x), one_mul]
  right_inv f := by
    funext x
    simp only [← mul_assoc, mul_inv_cancel₀ (ha x), one_mul]
  map_add' f g := by
    funext x
    exact mul_add _ _ _
  map_smul' c f := by
    funext x
    exact mul_left_comm _ _ _

/-- Multiplication by the square root of a strictly positive weight, in the
counting Euclidean Hilbert space. -/
def sqrtWeightEquiv (w : Ω → ℝ) (hw : ∀ x, 0 < w x) :
    EuclideanSpace ℂ Ω ≃ₗ[ℂ] EuclideanSpace ℂ Ω :=
  ((WithLp.linearEquiv 2 ℂ (Ω → ℂ)).trans
    (coordinateMulEquiv (fun x => (Real.sqrt (w x) : ℂ))
      (fun x => Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (hw x)))))).trans
    (WithLp.linearEquiv 2 ℂ (Ω → ℂ)).symm

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    sqrtWeightEquiv w hw f x = (Real.sqrt (w x) : ℂ) * f x := rfl

omit [Fintype Ω] in
@[simp]
theorem sqrtWeightEquiv_symm_apply (w : Ω → ℝ) (hw : ∀ x, 0 < w x)
    (f : EuclideanSpace ℂ Ω) (x : Ω) :
    (sqrtWeightEquiv w hw).symm f x = (Real.sqrt (w x) : ℂ)⁻¹ * f x := rfl

end InvertibleWeights

section Transport

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Transport a degree flag through an invertible linear weight operator. -/
def transportFlag (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E) (k : ℕ) :
    Submodule 𝕜 E := (F k).map D.toLinearMap

theorem transportFlag_zero (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (hF : F 0 = ⊥) : transportFlag D F 0 = ⊥ := by
  simp [transportFlag, hF]

theorem transportFlag_top (D : E ≃ₗ[𝕜] E) (F : ℕ → Submodule 𝕜 E)
    (k : ℕ) (hF : F k = ⊤) : transportFlag D F k = ⊤ := by
  simp [transportFlag, hF]

end Transport

section MatrixTransport

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]

/-- Matrix of an actual flag-layer projection in an orthonormal basis. -/
def flagProjectionMatrix (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (k : ℕ) : Matrix ι ι ℂ :=
  operatorMatrix b (flagProjection K k)

end MatrixTransport

section WeightedCube

variable {n : ℕ}

/-- The weighted degree-`k` subspace of the counting Hilbert space. -/
def weightedFourierSpace (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  (fourierEuclideanSpace n k).map (sqrtWeightEquiv w hw).toLinearMap

/-- The weighted Fourier flag, shifted by one so that stage zero is bottom. -/
def weightedFourierFlag (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    ℕ → Submodule ℂ (EuclideanSpace ℂ (Cube n)) :=
  transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)

@[simp]
theorem weightedFourierFlag_zero (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw 0 = ⊥ :=
  transportFlag_zero _ _ (fourierFlag_zero n)

@[simp]
theorem weightedFourierFlag_succ (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (k : ℕ) :
    weightedFourierFlag w hw (k + 1) = weightedFourierSpace w hw k := rfl

@[simp]
theorem weightedFourierFlag_top (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) :
    weightedFourierFlag w hw (n + 1) = ⊤ :=
  transportFlag_top _ _ _ (fourierFlag_top n)

/-- The projection represented in the point-mass orthonormal basis. -/
def weightedProjectionMatrix (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (k : Fin (n + 1)) : Matrix (Cube n) (Cube n) ℂ :=
  flagProjectionMatrix (EuclideanSpace.basisFun (Cube n) ℂ)
    (weightedFourierFlag w hw) k.val

end WeightedCube

end LeanBlast.GotsmanLinial

end

end OAI


