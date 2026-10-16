-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_Model
-- name    : OAI_Analysis_HyperbolicCones_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:24:14.04681+00:00
-- url     : https://prove2.me/theorems/62c7361d-3456-4b12-9f96-9ff7d8ff2d39
-- title:
--   The Choi–Lam form, Euclidean matrix tools, and normalized Schur-complement pencils
-- statement:
--   Throughout, $\mathrm{Sym}_n$ is the real vector space of symmetric real $n\times n$ matrices, $I$ (or $I_n$) is the identity matrix, and for a symmetric matrix $M$ we write $M\succeq0$ if $M$ is positive semidefinite and $M\succ0$ if it is positive definite. Vectors in $\mathbb{R}^3$ (or $R^3$) have indices $0,1,2$, read modulo $3$. A vector of $\mathbb{R}^4$ is written $v=(v_0,v_1,v_2,v_3)=(v_0,v')$ with $v'=(v_1,v_2,v_3)\in\mathbb{R}^3$. For $y\in\mathbb{R}^3$ let $Q(y)$ be the symmetric $3\times3$ matrix with $Q(y)_{ii}=y_i^2+y_{i+1}^2$ and $Q(y)_{ij}=-y_iy_j$ for $i\neq j$. For a $4\times4$ matrix $M$ (indices $0,\dots,3$) write $\alpha=M_{00}$, $b^{\mathsf T}=(M_{01},M_{02},M_{03})$ for the rest of its first row, $b'=(M_{10},M_{20},M_{30})^{\mathsf T}$ for the rest of its first column, and $M'$ for its lower-right $3\times3$ block, and put
--
--   $$
--   \varphi_y(M)=\begin{pmatrix}\operatorname{tr}\bigl(Q(y)M'\bigr) & -b^{\mathsf T}Q(y)\\ -Q(y)\,b' & \alpha\,Q(y)\end{pmatrix}.
--   $$
--
--   The file introduces the following objects.
--
--   1. **The Choi–Lam form.** For a commutative ring $R$ and $z,y\in R^3$,
--   $$
--   C(z,y)=\sum_{i=0}^{2}z_i^2y_i^2-2\bigl(z_0y_0z_1y_1+z_0y_0z_2y_2+z_1y_1z_2y_2\bigr)+\sum_{i=0}^{2}z_i^2y_{i+1}^2 .
--   $$
--   Expanding shows that $C(z,y)=z^{\mathsf T}Q(y)\,z$.
--   2. **The matrix $Z(z)$.** For $z\in R^3$, $Z(z)$ is the $3\times3$ matrix with $Z(z)_{ii}=z_i^2+z_{i+2}^2$ and $Z(z)_{ij}=-z_iz_j$ for $i\neq j$. It satisfies $y^{\mathsf T}Z(z)\,y=C(z,y)$, so it represents the same form as a quadratic form in $y$.
--   3. **Euclidean vectors and outer products.** $\mathbb{R}^n$ carries its standard inner product $\langle\cdot,\cdot\rangle$ and Euclidean norm $\|\cdot\|$. For $v\in\mathbb{R}^n$ the outer product $vv^{\mathsf T}$ is the matrix with entries $v_iv_j$, also regarded as an element of $\mathrm{Sym}_n$.
--   4. **Operator norm.** For $A\in\mathbb{R}^{m\times n}$, $\|A\|_{\mathrm{op}}=\sup\{\|Ax\| : x\in\mathbb{R}^n,\ \|x\|\le1\}$, the norm of $A$ as a map between Euclidean spaces (its largest singular value).
--   5. **Kernel projection.** For $A\in\mathbb{R}^{n\times n}$, $\Pi_{\ker A}$ is the matrix of the orthogonal projection of $\mathbb{R}^n$ onto the null space $\ker A$.
--   6. **Inverse square root.** If $H\in\mathrm{Sym}_n$ has spectral decomposition $H=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)\,U^{\mathsf T}$ with $U$ orthogonal, then $H^{-1/2}=U\operatorname{diag}(\mu_1,\dots,\mu_n)\,U^{\mathsf T}$, where $\mu_i=\lambda_i^{-1/2}$ if $\lambda_i>0$ and $\mu_i=0$ if $\lambda_i\le0$. For $H\succ0$ this is the usual inverse square root.
--   7. **Wedge coordinates.** For $v,u\in\mathbb{R}^4$, $w(v,u)=v_0u'-u_0v'\in\mathbb{R}^3$, that is, $w(v,u)_i=v_0u_{i+1}-u_0v_{i+1}$ for $i=0,1,2$.
--   8. **Tangent curves and tangent spaces.** For $v,h\in\mathbb{R}^4$ and $s\in\mathbb{R}$, $\gamma_{v,h}(s)=(1+s^2\|h\|^2)^{-1/2}(v+sh)$, and $T_v=\{h\in\mathbb{R}^4:\langle v,h\rangle=0\}$. If $\|v\|=1$ and $h\in T_v$, then $\gamma_{v,h}$ is a curve on the unit sphere with $\gamma_{v,h}(0)=v$ and velocity $h$ at $s=0$.
--   9. **Normalized pencils.** A normalized pencil consists of integers $a,c\ge1$ and linear maps $D:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$ and $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ such that $D$ and $E$ are positive ($X\succeq0$ implies $D(X)\succeq0$ and $E(X)\succeq0$), unital ($D(I_4)=I_a$ and $E(I_4)=I_c$), and for all $X,Z\in\mathrm{Sym}_4$ and $y\in\mathbb{R}^3$ with $X\succ0$
--   $$
--   Z-\varphi_y(X^{-1})\succeq0\iff E(Z)-B(y)^{\mathsf T}D(X)^{-1}B(y)\succeq0 .
--   $$
--   For such a pencil and $v\in\mathbb{R}^4$, the left and right projections are $P_v=\Pi_{\ker D(I_4-vv^{\mathsf T})}$, acting on $\mathbb{R}^a$, and $R_v=\Pi_{\ker E(I_4-vv^{\mathsf T})}$, acting on $\mathbb{R}^c$.
--
--   These are the basic objects of an argument showing that a certain hyperbolicity cone in $\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$ has no spectrahedral representation. On the slice $X\succ0$ that cone is described by the condition $Z-\varphi_y(X^{-1})\succeq0$. The right-hand side of the equivalence in item 9 is the Schur-complement form of the condition $\begin{pmatrix}D(X)&B(y)\\B(y)^{\mathsf T}&E(Z)\end{pmatrix}\succeq0$. A normalized pencil is therefore the normal form to which a hypothetical spectrahedral representation is reduced. The remaining objects are used to rule such a pencil out. The later argument compares the Choi–Lam form at wedge coordinates with squared operator norms such as $\|P_vB(y)R_u\|_{\mathrm{op}}^2$ for unit vectors $u,v$, and it differentiates kernel projections along tangent curves.
--
--   **Formalization Note** `Vec n` is `EuclideanSpace ℝ (Fin n)`. `choiLam` and `zMatrix` are defined over an arbitrary commutative ring. `outer v` is the matrix $vv^{\mathsf T}$ and `outerSym v` is the same matrix as an element of `Sym n`. `operatorNorm` is the norm of the continuous linear map attached to the matrix by `Matrix.toEuclideanLin`, and `kernelProjection` is the matrix of `starProjection` onto the kernel. `inverseSquareRoot` is built from Mathlib's `eigenvectorUnitary` and `eigenvalues`; the convention $\mu_i=0$ for $\lambda_i\le0$ comes from `Real.sqrt` vanishing on negative numbers and from the inverse of $0$ being $0$. In `NormalizedPencil` the inverses are Lean's total matrix inverse, but for $X\succ0$ both $X$ and $D(X)$ are invertible, the latter because positivity and unitality give $D(X)\succeq\lambda_{\min}(X)\,I_a$. Mathlib's `PosSemidef` includes symmetry. The structure fields are `D_positive`, `E_positive`, `D_unital`, `E_unital` and `schur_equivalence`, and the projections are `leftProjection` and `rightProjection`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones

namespace OAI

/-! The Choi–Lam form, determinant polynomial, root-defined cone, and quadratic deformation. -/

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

def choiLam {R : Type u} [CommRing R] (z y : Fin 3 → R) : R :=
  (∑ i, z i ^ 2 * y i ^ 2) -
    2 * (z 0 * y 0 * z 1 * y 1 + z 0 * y 0 * z 2 * y 2 +
      z 1 * y 1 * z 2 * y 2) +
    (∑ i, z i ^ 2 * y (i + 1) ^ 2)

def zMatrix {R : Type u} [CommRing R] (z : Fin 3 → R) : Mat 3 R :=
  fun i j => if i = j then z i ^ 2 + z (i + 2) ^ 2 else -(z i * z j)

open scoped BigOperators RealInnerProductSpace
open Set Filter Matrix

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

def outer {n : ℕ} (v : Vec n) : Mat n ℝ := fun i j => v i * v j

def outerSym {n : ℕ} (v : Vec n) : Sym n :=
  ⟨outer v, by
    change (outer v)ᴴ = outer v
    ext i j
    simp [outer, Matrix.conjTranspose_apply, mul_comm]⟩

def operatorNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def kernelProjection {n : ℕ} (A : Mat n ℝ) : Mat n ℝ :=
  Matrix.toEuclideanLin.symm (A.toEuclideanLin.ker.starProjection.toLinearMap)

def inverseSquareRoot {n : ℕ} (A : Sym n) : Mat n ℝ :=
  let hA : (A : Mat n ℝ).IsHermitian := A.property
  let U : Mat n ℝ := hA.eigenvectorUnitary
  U * Matrix.diagonal (fun i => (Real.sqrt (hA.eigenvalues i))⁻¹) * Uᴴ

/-- The vector v₀u′−u₀v′ in the rank-one and operator-norm identities. -/
def wedgeCoordinates (v u : Vec 4) : Fin 3 → ℝ :=
  fun i => v 0 * u i.succ - u 0 * v i.succ

def tangentCurve (v h : Vec 4) (s : ℝ) : Vec 4 :=
  (Real.sqrt (1 + s ^ 2 * ‖h‖ ^ 2))⁻¹ • (v + s • h)

def tangentSpace (v : Vec 4) : Submodule ℝ (Vec 4) := (innerSL ℝ v).ker

/-- Positive unital diagonal blocks with an exact Schur-complement equivalence. -/
structure NormalizedPencil where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  D : Sym 4 →ₗ[ℝ] Sym a
  E : Sym 4 →ₗ[ℝ] Sym c
  B : (Fin 3 → ℝ) →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ
  D_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (D X : Mat a ℝ).PosSemidef
  E_positive : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (E X : Mat c ℝ).PosSemidef
  D_unital : D 1 = 1
  E_unital : E 1 = 1
  schur_equivalence : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ) (_hX : (X : Mat 4 ℝ).PosDef),
    ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef ↔
      ((E Z : Mat c ℝ) - (B y)ᵀ * (D X : Mat a ℝ)⁻¹ * B y).PosSemidef

def NormalizedPencil.leftProjection (P : NormalizedPencil) (v : Vec 4) : Mat P.a ℝ :=
  kernelProjection (P.D (1 - outerSym v) : Mat P.a ℝ)

def NormalizedPencil.rightProjection (P : NormalizedPencil) (v : Vec 4) : Mat P.c ℝ :=
  kernelProjection (P.E (1 - outerSym v) : Mat P.c ℝ)

end Paper256

end

end OAI


