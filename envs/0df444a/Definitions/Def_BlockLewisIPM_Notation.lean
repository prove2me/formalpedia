-- Prove2me | Definitions.Def_BlockLewisIPM_Notation
-- name    : BlockLewisIPM_Notation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:12.516081+00:00
-- url     : https://prove2.me/theorems/5a7637a2-69d9-4379-b584-cdbbe52bf648
-- title:
--   Block notation, Loewner order, projections, the Fenchel conjugate and the Bregman divergence
-- statement:
--   This file fixes the linear-algebra vocabulary of the paper.
--
--   A coordinate of $\mathbb R^n$ is a pair (block $i$, position in block $i$), so a vector $v$ has blocks $v_i\in\mathbb R^{n_i}$, and $\operatorname{diag}_G(w)$ lifts $w\in\mathbb R^m$ to the block diagonal matrix with blocks $w_iI_{n_i}$. The block trace is $\operatorname{tr}_G(M)=(\operatorname{tr}M_1,\dots,\operatorname{tr}M_m)$.
--
--   For symmetric matrices, $A\preceq B$ means that $B-A$ is positive semidefinite, and
--
--   $$A\approx_\epsilon B\quad\Longleftrightarrow\quad e^{-\epsilon}B\preceq A\preceq e^{\epsilon}B;$$
--
--   for vectors, $a\approx_\epsilon b$ means $e^{-\epsilon}b_i\le a_i\le e^{\epsilon}b_i$ for all $i$. The local norm is $\|v\|_B=\sqrt{v^\top Bv}$, and $\operatorname{sym}(A)=(A+A^\top)/2$. For full column rank, $P(B)=B(B^\top B)^{-1}B^\top$ is the orthogonal projection onto the column space of $B$.
--
--   The Fenchel conjugate of a barrier $\phi$ on $K$ and the Bregman divergence of $f$ are
--
--   $$\phi^*(y)=\sup_{x\in\operatorname{int}K}\langle x,y\rangle-\phi(x),\qquad D_f(a,b)=f(a)-f(b)-\langle\nabla f(b),a-b\rangle .$$
--
--   These objects are used in every later definition.
--
--   **Formalization Note** Matrix roots are the continuous functional calculus square root, and $M^{-1/2}$ is the inverse of the root. Both inverse and root have junk values off the positive definite matrices, so statements carry the conditions excluding those inputs. The conjugate's supremum runs over $\operatorname{int}K$, the domain of the barrier in §2.1.
-- source:
--   Zhang, Wright, A Fast Lewis-weight Interior Point Method for Linear Optimization over Product-Domain (manuscript, sha256 66072000…), §3.1, p.10; Definition 4, p.11; Definition 7, p.12

import Mathlib

namespace BlockLewisIPM

/-!
# Matrix, block and barrier vocabulary

Zhang, Wright, *A Fast Lewis-weight Interior Point Method for Linear Optimization over
Product-Domain* (manuscript, sha256 66072000…), §3.1, p.10, Definition 4, p.11, and Definition 7,
p.12.

**Formalization Note.**
* The block partition `G` of p.10 is the sigma type `Σ i, Fin (dim i)` (reading R8): a coordinate of
  `ℝⁿ` is a pair (block, position in block). Consecutive numbering enters only in the machine's
  memory layout. `diagG` lifts `w ∈ ℝ^m` to the block diagonal matrix with blocks `w_i I_{n_i}`.
* `A ⪯ B` is `(B - A).PosSemidef`, which forces symmetry. `A ≈_ϵ B` is `e^{-ϵ} B ⪯ A ⪯ e^{ϵ} B`, and
  `a ≈_ϵ b` for vectors is `e^{-ϵ} b_i ≤ a_i ≤ e^{ϵ} b_i`, both as on p.10.
* Matrix roots are `CFC.sqrt`, and `M^{-1/2}` is `(CFC.sqrt M)⁻¹`. `CFC.sqrt` is junk off the positive
  semidefinite matrices and `⁻¹` is `0` on singular matrices, so every statement using them carries
  the positive definiteness or the domain condition that excludes those inputs.
* `P(B) = B (B⊤B)⁻¹ B⊤` is defined on p.10 for full column rank; `FullColRank` is the hypothesis
  every statement using it carries (reading R10).
* Barrier derivatives are `fderiv` and `iteratedFDeriv` in the standard basis, the form the barrier
  predicate and the machine's oracle both read.
* Definition 4's supremum over `x ∈ K` is taken over `int K`, the domain of the barrier (§2.1, p.3,
  `ϕ_i : int(K_i) → ℝ`; reading R6).
-/

open Matrix

/-- `ℝᵏ` with its Euclidean norm. -/
abbrev Eu (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `X ⪯ Y`: the difference `Y - X` is positive semidefinite (p.10). -/
def LoewnerLE {a : Type*} [Fintype a] (X Y : Matrix a a ℝ) : Prop := (Y - X).PosSemidef

/-- `X ≈_ϵ Y`: `e^{-ϵ} Y ⪯ X ⪯ e^{ϵ} Y` (p.10). -/
def ApproxEq {a : Type*} [Fintype a] (ϵ : ℝ) (X Y : Matrix a a ℝ) : Prop :=
  LoewnerLE (Real.exp (-ϵ) • Y) X ∧ LoewnerLE X (Real.exp ϵ • Y)

/-- `a ≈_ϵ b` for vectors: `e^{-ϵ} b_i ≤ a_i ≤ e^{ϵ} b_i` (p.10). -/
def VecApproxEq {a : Type*} (ϵ : ℝ) (u v : a → ℝ) : Prop :=
  ∀ i, Real.exp (-ϵ) * v i ≤ u i ∧ u i ≤ Real.exp ϵ * v i

/-- `‖v‖_B = √(v⊤ B v)` (p.10). -/
noncomputable def wNorm {a : Type*} [Fintype a] (B : Matrix a a ℝ) (v : a → ℝ) : ℝ :=
  Real.sqrt (v ⬝ᵥ (B *ᵥ v))

/-- The Euclidean norm `‖v‖₂`. -/
noncomputable def eNorm {a : Type*} [Fintype a] (v : a → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

open scoped Matrix.Norms.L2Operator in
/-- The operator norm `‖M‖_op`, for the Euclidean norms on both sides (p.10). -/
noncomputable def opNorm {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (M : Matrix a b ℝ) : ℝ := ‖M‖

/-- `sym(A) = (A + A⊤)/2` (p.10). -/
noncomputable def sym {a : Type*} (M : Matrix a a ℝ) : Matrix a a ℝ := (1 / 2 : ℝ) • (M + Mᵀ)

open scoped MatrixOrder in
/-- The matrix square root `M^{1/2}`. -/
noncomputable def matSqrt {a : Type*} [Fintype a] [DecidableEq a] (M : Matrix a a ℝ) :
    Matrix a a ℝ :=
  CFC.sqrt M

/-- The inverse square root `M^{-1/2}`. -/
noncomputable def matInvSqrt {a : Type*} [Fintype a] [DecidableEq a] (M : Matrix a a ℝ) :
    Matrix a a ℝ :=
  (matSqrt M)⁻¹

/-- `P(B) = B (B⊤B)⁻¹ B⊤`, the orthogonal projection onto the column space when `B` has full column
rank (p.10). -/
noncomputable def projMat {a : Type*} [Fintype a] {d : ℕ} (B : Matrix a (Fin d) ℝ) :
    Matrix a a ℝ :=
  B * (Bᵀ * B)⁻¹ * Bᵀ

/-- Full column rank (p.10). -/
def FullColRank {a : Type*} [Fintype a] {d : ℕ} (B : Matrix a (Fin d) ℝ) : Prop := B.rank = d

/-- The gradient of `φ` at `x`, in the standard basis. -/
noncomputable def gradVec {k : ℕ} (φ : Eu k → ℝ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun j => fderiv ℝ φ (WithLp.toLp 2 x) (EuclideanSpace.single j 1)

/-- The Hessian of `φ` at `x`, in the standard basis. -/
noncomputable def hessMat {k : ℕ} (φ : Eu k → ℝ) (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun j l =>
    iteratedFDeriv ℝ 2 φ (WithLp.toLp 2 x) ![EuclideanSpace.single j 1, EuclideanSpace.single l 1]

/-- The Fenchel conjugate `ϕ*(y) = sup_{x ∈ int K} ⟨x, y⟩ - ϕ(x)` of Definition 4, p.11. -/
noncomputable def conj {k : ℕ} (K : Set (Eu k)) (φ : Eu k → ℝ) : Eu k → ℝ :=
  fun y => sSup ((fun x : Eu k => inner ℝ x y - φ x) '' interior K)

/-- The Bregman divergence `D_f(a, b) = f(a) - f(b) - ⟨∇f(b), a - b⟩` of Definition 7, p.12. -/
noncomputable def bregman {k : ℕ} (f : Eu k → ℝ) (a b : Fin k → ℝ) : ℝ :=
  f (WithLp.toLp 2 a) - f (WithLp.toLp 2 b) - gradVec f b ⬝ᵥ (a - b)

section Blocks

variable {ι : Type} (dim : ι → ℕ)

/-- The coordinates of `ℝⁿ`, by block (the partition `G` of p.10, reading R8). -/
abbrev BIdx := Σ i, Fin (dim i)

variable {dim}

/-- The block `v_i` of `v`. -/
def block (v : BIdx dim → ℝ) (i : ι) : Fin (dim i) → ℝ := fun l => v ⟨i, l⟩

/-- The block `v_i` of `v`, as a point of `ℝ^{n_i}`. -/
def blockPt (v : BIdx dim → ℝ) (i : ι) : Eu (dim i) := WithLp.toLp 2 (block v i)

/-- The vector with blocks `v i`. -/
def glue (v : ∀ i, Fin (dim i) → ℝ) : BIdx dim → ℝ := fun j => v j.1 j.2

/-- `diag_G(w)`: the block diagonal matrix with blocks `w_i I_{n_i}` (p.10). -/
def diagG [DecidableEq ι] (w : ι → ℝ) : Matrix (BIdx dim) (BIdx dim) ℝ :=
  Matrix.diagonal fun j => w j.1

/-- The block trace: `tr_G(M)_i = tr(M_i)` (p.10). -/
def blockTrace (M : Matrix (BIdx dim) (BIdx dim) ℝ) (i : ι) : ℝ :=
  ∑ l, M ⟨i, l⟩ ⟨i, l⟩

/-- `(‖v_i‖₂)_i`. -/
noncomputable def blockNorms (v : BIdx dim → ℝ) : ι → ℝ := fun i => eNorm (block v i)

/-- `‖u‖_∞`. -/
noncomputable def supNorm [Fintype ι] (u : ι → ℝ) : ℝ := ⨆ i, |u i|

/-- `‖v‖_{2,∞} = max_i ‖v_i‖₂` (p.13). -/
noncomputable def blockSupNorm [Fintype ι] (v : BIdx dim → ℝ) : ℝ := supNorm (blockNorms v)

/-- `‖u‖_τ = (∑ τ_i u_i²)^{1/2}`: the norm `‖·‖_{diag(τ)}` of p.10. -/
noncomputable def wtNorm [Fintype ι] (τ u : ι → ℝ) : ℝ := Real.sqrt (∑ i, τ i * u i ^ 2)

end Blocks

end BlockLewisIPM


