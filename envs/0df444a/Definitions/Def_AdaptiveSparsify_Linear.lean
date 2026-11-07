-- Prove2me | Definitions.Def_AdaptiveSparsify_Linear
-- name    : AdaptiveSparsify_Linear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:04.607757+00:00
-- url     : https://prove2.me/theorems/e12deafb-2e21-4d51-8b71-eebfc3535631
-- title:
--   Loewner order, $A\approx_\alpha B$, local norms, leverage, matrix roots, barrier derivatives, and block notation
-- statement:
--   The basic vocabulary of the mission.
--
--   For symmetric matrices, $X\preceq Y$ means that $Y-X$ is positive semidefinite, and
--
--   $$X\approx_\alpha Y\quad\Longleftrightarrow\quad e^{-\alpha}X\preceq Y\preceq e^{\alpha}X.$$
--
--   For a matrix $M$ and a vector $v$, the local norm is $\|v\|_M=(v^\top Mv)^{1/2}$. The leverage of a row $a$ against a Gram matrix $G$ is $a^\top G^{-1}a$. A block structure consists of $m$ blocks of dimensions $n_i$, with $n=\sum_i n_i$; the vector $x_i$ is the restriction of $x\in\mathbb R^n$ to block $i$, and block diagonal matrices are assembled from their blocks. Gradients and Hessians of a barrier are the Fréchet derivatives in the standard basis, the same objects for the machine, for the interior point objects and for the barrier predicate.
--
--   These notions are shared by every statement of the mission.
--
--   **Formalization Note** Blocks are consecutive runs of coordinates, which differs from the arbitrary coordinate sets $S_i$ of p.10 by a permutation of the rows of $A$ and the entries of $c$. Matrix roots use the continuous functional calculus and $M^{-1/2}$ is the inverse of $M^{1/2}$; both are junk off the positive definite matrices, so every statement using them carries a domain or positive definiteness condition.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), §2.1–§2.2, p.10; §4, pp.17–18

import Mathlib

namespace AdaptiveSparsify

/-!
# Matrix and block vocabulary

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification with Applications to Empirical Risk
Minimization and Computational Geometry* (manuscript, sha256 7a66a27b…), §2.1–§2.2, p.10, and the
norm notation of §4, pp.17–18.

**Formalization Note.**
* The Loewner order `A ⪯ B` of p.10 is `(B - A).PosSemidef`, so both sides are forced symmetric.
* `A ≈_α B` is `e^{-α} A ⪯ B ⪯ e^{α} A`, as on p.10.
* Blocks are consecutive runs of coordinates of `Fin (∑ i, dim i)` through `finSigmaFinEquiv`
  (reading R8): p.10's arbitrary coordinate sets `S_i` differ from this by a permutation of the
  rows of `A` and the entries of `c`.
* Matrix roots are `CFC.sqrt`, and `M^{-1/2}` is `(CFC.sqrt M)⁻¹`. `CFC.sqrt` is junk off the
  positive semidefinite matrices and `⁻¹` is `0` on singular matrices, so every statement that uses
  them carries the positive definiteness or the domain condition that excludes those inputs.
* Barrier derivatives are `fderiv` and `iteratedFDeriv` in the standard basis, read in the same form
  by the machine, the interior point objects and the barrier definition.
-/

open Matrix

/-- `X ⪯ Y`: the difference `Y - X` is positive semidefinite (p.10). -/
def LoewnerLE {ι : Type*} [Fintype ι] (X Y : Matrix ι ι ℝ) : Prop := (Y - X).PosSemidef

/-- `X ≈_α Y`: `e^{-α} X ⪯ Y ⪯ e^{α} X` (p.10). -/
def ApproxEq {ι : Type*} [Fintype ι] (α : ℝ) (X Y : Matrix ι ι ℝ) : Prop :=
  LoewnerLE (Real.exp (-α) • X) Y ∧ LoewnerLE Y (Real.exp α • X)

/-- The quadratic form `v⊤ M v`. -/
def quadForm {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ := v ⬝ᵥ (M *ᵥ v)

/-- The local norm `‖v‖_M = (v⊤ M v)^{1/2}`. -/
noncomputable def wNorm {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  Real.sqrt (quadForm M v)

/-- The Euclidean norm `‖v‖₂`. -/
noncomputable def eNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The leverage of a row `a` against a Gram matrix `G`: `a⊤ G⁻¹ a`. -/
noncomputable def leverage {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (a : ι → ℝ) :
    ℝ :=
  a ⬝ᵥ (G⁻¹ *ᵥ a)

open scoped MatrixOrder in
/-- The matrix square root `M^{1/2}`. -/
noncomputable def matSqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  CFC.sqrt M

/-- The inverse square root `M^{-1/2}`. -/
noncomputable def matInvSqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  (matSqrt M)⁻¹

/-- The gradient of `φ` at `x`, in the standard basis. -/
noncomputable def gradVec {k : ℕ} (φ : EuclideanSpace ℝ (Fin k) → ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun j => fderiv ℝ φ (WithLp.toLp 2 x) (EuclideanSpace.single j 1)

/-- The Hessian of `φ` at `x`, in the standard basis. -/
noncomputable def hessMat {k : ℕ} (φ : EuclideanSpace ℝ (Fin k) → ℝ) (x : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j l =>
    iteratedFDeriv ℝ 2 φ (WithLp.toLp 2 x) ![EuclideanSpace.single j 1, EuclideanSpace.single l 1]

/-- A block structure: `m` blocks of dimensions `dim i`. -/
structure Blocks where
  /-- The number of blocks. -/
  m : ℕ
  /-- The block dimensions `n_i`. -/
  dim : Fin m → ℕ

namespace Blocks

/-- The total dimension `n = ∑ n_i`. -/
def n (B : Blocks) : ℕ := ∑ i, B.dim i

/-- Coordinate `l` of block `i`, as a coordinate of `ℝⁿ`. -/
def coord (B : Blocks) (i : Fin B.m) (l : Fin (B.dim i)) : Fin B.n :=
  finSigmaFinEquiv ⟨i, l⟩

/-- The block containing coordinate `j`. -/
def blockOf (B : Blocks) (j : Fin B.n) : Fin B.m := (finSigmaFinEquiv.symm j).1

/-- The restriction `x_i` of `x` to block `i`. -/
def restrict (B : Blocks) (x : Fin B.n → ℝ) (i : Fin B.m) : Fin (B.dim i) → ℝ :=
  fun l => x (B.coord i l)

/-- The vector whose restriction to block `i` is `v i`. -/
def glue (B : Blocks) (v : ∀ i, Fin (B.dim i) → ℝ) : Fin B.n → ℝ :=
  fun j => v (finSigmaFinEquiv.symm j).1 (finSigmaFinEquiv.symm j).2

/-- The block diagonal `n × n` matrix with blocks `M i`. -/
noncomputable def assemble (B : Blocks) (M : ∀ i, Matrix (Fin (B.dim i)) (Fin (B.dim i)) ℝ) :
    Matrix (Fin B.n) (Fin B.n) ℝ :=
  (Matrix.blockDiagonal' M).submatrix finSigmaFinEquiv.symm finSigmaFinEquiv.symm

end Blocks

end AdaptiveSparsify


