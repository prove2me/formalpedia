-- Prove2me | Definitions.Def_YeIPA_QPApprox_Relaxation
-- name    : YeIPA_QPApprox_Relaxation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:03.221479+00:00
-- url     : https://prove2.me/theorems/a3f1331e-f7cd-4a09-984f-a5b67d71646c
-- title:
--   The quadratic program with quadratic equality constraints and box bounds, its semidefinite relaxation (9.48), the dual (9.49), and the sphere rounding (9.50)
-- statement:
--   Fix $n,m\ge0$, a real $n\times n$ matrix $Q$, a real $m\times n$ matrix $A=\{a_{ij}\}$ with rows $a_i=(a_{i1},\dots,a_{in})$, and $b\in\mathbb R^m$. Vector inequalities are componentwise and $e$ is the all-ones vector. This module defines the objects of §9.5 of Ye's *Interior Point Algorithms*:
--
--   1. The objective $q(x)=x^TQx$ and the **quadratic program** (QP): $x\in\mathbb R^n$ is feasible if $\sum_{j=1}^n a_{ij}x_j^2=b_i$ for $i=1,\dots,m$ and $-e\le x\le e$. Its optimal value $\underline q(Q)$ is the infimum of $q$ over the feasible set, and $\bar q=-\underline q(-Q)$.
--   2. The matrix inner product $P\bullet X=\sum_{i,j}P_{ij}X_{ij}$, the matrices $A_i=\operatorname{diag}(a_i)$, the diagonal vector $d(X)=(X_{11},\dots,X_{nn})$, and the diagonal matrix $D(z)$ with $d(D(z))=z$.
--   3. The **semidefinite relaxation** (9.48): a symmetric $X$ is feasible if
--   $$A_i\bullet X=b_i\ (i=1,\dots,m),\qquad d(X)\le e,\qquad X\succeq0 .$$
--   Its optimal value $\underline p(Q)$ is the infimum of $Q\bullet X$ over this set, $\bar p=-\underline p(-Q)$, and an **optimal solution** $\underline X(Q)$ is a feasible $X$ with $Q\bullet X\le Q\bullet X'$ for every feasible $X'$.
--   4. The **dual** (9.49): $(y,z)\in\mathbb R^m\times\mathbb R^n$ is dual feasible if $Q-D(z)-\sum_{i}y_iA_i\succeq0$ and $z\le0$; its objective is $e^Tz+b^Ty$; a dual **optimal solution** is a dual feasible pair whose objective is at least that of every dual feasible pair.
--   5. For a function $f$ of one variable, $f[X]$ is the matrix with entries $f(x_{ij})$. With $D=\operatorname{diag}(\sqrt{x_{11}},\dots,\sqrt{x_{nn}})$, the matrix $D\arcsin[D^{-1}XD^{-1}]D$.
--   6. $\operatorname{sign}(t)=1$ if $t\ge0$ and $-1$ otherwise; $\sigma(x)$ is the vector with components $\operatorname{sign}(x_j)$. For $V\in\mathbb R^{n\times n}$ with columns $v_1,\dots,v_n$, $D=\operatorname{diag}(\|v_1\|,\dots,\|v_n\|)$ (Euclidean norms), and for $u$ on the unit sphere the **rounded point** (9.50)
--   $$\hat x=D\,\sigma(V^Tu).$$
--   7. The uniform probability measure on the unit sphere $\{u\in\mathbb R^n:\|u\|=1\}$.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$. $\underline q(Q)$ and $\underline p(Q)$ are real infima (`sInf`) of the sets of feasible objective values; both sets are bounded (the feasible sets are compact), and every theorem assumes the QP is feasible, which makes them nonempty, so these infima are attained minima. $X\succeq0$ is Mathlib's `PosSemidef`, which includes symmetry. The inverse $D^{-1}$ is Mathlib's matrix inverse, which is the true inverse when every $x_{jj}>0$ (the only case the book uses it, $X\succ0$). The uniform measure is the surface measure `volume.toSphere` on the unit sphere of `EuclideanSpace ℝ (Fin n)` divided by its total mass; it is a probability measure for $n\ge1$.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 325 (QP, (9.48)), p. 326 (A_i, d(X), (9.49), D(z)), p. 327 ((9.50), sign, σ), p. 328 (f[X], D in Theorem 9.32)

import Mathlib

open Matrix MeasureTheory

namespace YeIPA.QPApprox

/-!
# The quadratic program of §9.5, its positive semi-definite relaxation and the sphere rounding

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997, §9.5: the QP and `q̲(Q)` p. 325;
the relaxation (9.48) p. 325; `A_i = diag(a_i)`, `d(X)`, the dual (9.49), `D(z)` p. 326; the
rounding (9.50), `D = diag(‖v_1‖, …, ‖v_n‖)`, `σ` and `sign` p. 327; `f[X]` p. 328.

`Q : Matrix (Fin n) (Fin n) ℝ`, `A : Matrix (Fin m) (Fin n) ℝ` with rows `a_i`, `b : Fin m → ℝ`.
The book's indices `1, …, n` are `0, …, n-1` here. Vector inequalities are componentwise.
-/

variable {m n : ℕ}

/-- The objective `q(x) = xᵀQx`. -/
def quadForm (Q : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (Q *ᵥ x)

/-- Feasibility for the QP of p. 325: `∑ⱼ a_ij x_j² = b_i` for every `i`, and `−e ≤ x ≤ e`. -/
def IsQPFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, ∑ j, A i j * x j ^ 2 = b i) ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1

/-- `q̲(Q)`: the minimal value of `q(x) = xᵀQx` over the QP's feasible set (p. 325), taken as
the infimum of the set of feasible objective values. -/
noncomputable def qpMin (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : ℝ :=
  sInf (quadForm Q '' {x | IsQPFeasible A b x})

/-- `q̄ := −q̲(−Q)` (p. 325). -/
noncomputable def qpMax (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : ℝ :=
  -qpMin (-Q) A b

/-- The matrix inner product `P • X = ∑ᵢ ∑ⱼ P_ij X_ij`. -/
def frob (P X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, P i j * X i j

/-- `A_i = diag(a_i)` with `a_i = (a_i1, …, a_in)` the `i`-th row of `A` (p. 326). -/
def constrMat (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => A i j)

/-- `d(X)`: the vector of diagonal entries of `X` (p. 326). -/
def diagVec (X : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ := fun j => X j j

/-- `D(z)`: the diagonal matrix with `d(D(z)) = z` (p. 326). -/
def diagMat (z : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal z

/-- Feasibility for the relaxation (9.48): `A_i • X = b_i` for every `i`, `d(X) ≤ e`, `X ⪰ 0`
(positive semi-definite, in particular symmetric). -/
def IsRelaxFeasible (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, frob (constrMat A i) X = b i) ∧ (∀ j, diagVec X j ≤ 1) ∧ X.PosSemidef

/-- `p̲(Q)`: the minimal value of `Q • X` over the feasible set of (9.48), taken as the infimum
of the set of feasible objective values. -/
noncomputable def sdpMin (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : ℝ :=
  sInf (frob Q '' {X | IsRelaxFeasible A b X})

/-- `p̄ := −p̲(−Q)` (Proposition 9.29, p. 326). -/
noncomputable def sdpMax (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : ℝ :=
  -sdpMin (-Q) A b

/-- An optimal solution `X̲(Q)` of (9.48): feasible, and `Q • X ≤ Q • X'` for every feasible
`X'`. -/
def IsRelaxOptimal (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRelaxFeasible A b X ∧ ∀ X', IsRelaxFeasible A b X' → frob Q X ≤ frob Q X'

/-- Feasibility for the dual (9.49): `Q ⪰ D(z) + ∑ᵢ y_i A_i` and `z ≤ 0`. -/
def IsDualFeasible (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (y : Fin m → ℝ) (z : Fin n → ℝ) : Prop :=
  (Q - (diagMat z + ∑ i, y i • constrMat A i)).PosSemidef ∧ ∀ j, z j ≤ 0

/-- The dual objective `eᵀz + bᵀy` of (9.49). -/
def dualObj (b : Fin m → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) : ℝ := ∑ j, z j + b ⬝ᵥ y

/-- An optimal solution `(y̲(Q), z̲(Q))` of the dual (9.49): feasible, and with dual objective
at least that of every dual feasible pair. -/
def IsDualOptimal (Q : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (y : Fin m → ℝ) (z : Fin n → ℝ) : Prop :=
  IsDualFeasible Q A y z ∧
    ∀ y' z', IsDualFeasible Q A y' z' → dualObj b y' z' ≤ dualObj b y z

/-- `f[X]`: the matrix with entries `f(x_ij)` (p. 328). -/
def entrywise (f : ℝ → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => f (X i j)

/-- `D = diag(√x_11, …, √x_nn)` (Theorem 9.32, p. 328). -/
noncomputable def sqrtDiag (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => Real.sqrt (X j j))

/-- `D arcsin[D⁻¹ X D⁻¹] D` with `D = diag(√x_11, …, √x_nn)` (Theorem 9.32, p. 328). The
inverse is Mathlib's matrix inverse; it is the true inverse whenever every `x_jj > 0`, in
particular for `X ≻ 0`, the only case in which the book uses it. -/
noncomputable def arcsinTransform (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  sqrtDiag X * entrywise Real.arcsin ((sqrtDiag X)⁻¹ * X * (sqrtDiag X)⁻¹) * sqrtDiag X

/-- `sign(t) = 1` if `t ≥ 0` and `−1` otherwise (p. 327; note `sign(0) = 1`). -/
noncomputable def sign (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

/-- `σ(x)`: the vector whose `j`-th component is `sign(x_j)` (p. 327). -/
noncomputable def sigma (x : Fin n → ℝ) : Fin n → ℝ := fun j => sign (x j)

/-- `‖v_j‖`: the Euclidean norm of the `j`-th column `v_j` of `V` (p. 326). -/
noncomputable def colNorm (V : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  Real.sqrt (∑ k, V k j ^ 2)

/-- `D = diag(‖v_1‖, …, ‖v_n‖)` for `V = (v_1, …, v_n)` (p. 327). -/
noncomputable def colNormDiag (V : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (colNorm V)

/-- The uniform (normalized surface) probability measure on the unit sphere of `ℝⁿ`. -/
noncomputable def sphereUniform (n : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- The coordinates of a point `u` of the unit sphere, as a vector `Fin n → ℝ`. -/
def coords (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : Fin n → ℝ :=
  fun k => (u : EuclideanSpace ℝ (Fin n)) k

/-- The rounded point (9.50): `x̂ = Dσ(Vᵀu)` with `D = diag(‖v_1‖, …, ‖v_n‖)`. -/
noncomputable def roundedPoint (V : Matrix (Fin n) (Fin n) ℝ)
    (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : Fin n → ℝ :=
  colNormDiag V *ᵥ sigma (Vᵀ *ᵥ coords u)

end YeIPA.QPApprox


