-- Prove2me | Definitions.Def_ModernConvex_MatrixCube_MatrixCube
-- name    : ModernConvex_MatrixCube_MatrixCube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:05.765198+00:00
-- url     : https://prove2.me/theorems/b04d3d8b-91fb-4252-b1ed-9d89918da63d
-- title:
--   Matrix cube (4.4.35), the LMI system (S_ρ), the function θ of (4.4.38), and the radii R[A₁,…,A_m : A₀], ρ[A₁,…,A_m : A₀]
-- statement:
--   This file fixes the objects of the matrix cube problem (Ben-Tal–Nemirovski, §4.4.3, pp. 189–194).
--
--   1. For a symmetric $n\times n$ real matrix $X$, $\lambda(X)\in\mathbb R^n$ is the vector of its eigenvalues (with multiplicity) and $\|\lambda(X)\|_1=\sum_i|\lambda_i(X)|$.
--   2. The **standard Gaussian density** on $\mathbb R^k$ is $p_k(u)=(2\pi)^{-k/2}\exp\{-u^Tu/2\}$ (p. 190).
--   3. The function $\theta$ of (4.4.38) (p. 191) is, for $k\ge 1$,
--   $$\theta(k)=\frac{1}{\min\left\{\int_{\mathbb R^k}|\alpha_1u_1^2+\cdots+\alpha_ku_k^2|\,p_k(u)\,du \;\middle|\; \alpha\in\mathbb R^k,\ \|\alpha\|_1=1\right\}}.$$
--   4. Given $A_0,A_1,\dots,A_m\in\mathbf S^n$ and $\rho\in\mathbb R$, the **matrix cube** (4.4.35) is
--   $$\mathcal A_\rho=\Big\{A_0+\sum_{i=1}^m z_iA_i \;\Big|\; \|z\|_\infty\le\rho\Big\},$$
--   and "$\mathcal A_\rho\subset\mathbf S^n_+$" means every matrix of $\mathcal A_\rho$ is positive semidefinite.
--   5. Symmetric matrices $X^1,\dots,X^m$ **solve the system of LMIs $(S_\rho)$** (p. 190) if $X^i\succeq\rho A_i$ and $X^i\succeq-\rho A_i$ for $i=1,\dots,m$, and $\sum_{i=1}^mX^i\preceq A_0$; the system is **solvable** if such matrices exist.
--   6. $R[A_1,\dots,A_m:A_0]$ (p. 189) is the largest $\rho\ge0$ with $\mathcal A_\rho\subset\mathbf S^n_+$, and $\rho[A_1,\dots,A_m:A_0]$ is the optimal value of the semidefinite problem (4.4.45) (p. 194), the largest $\rho$ for which $(S_\rho)$ is solvable. Both are taken as suprema in $[-\infty,+\infty]$, so that the value $+\infty$ (when every $\rho$ qualifies, e.g. all $A_i=0$) is represented.
--
--   These are the objects of Proposition 4.4.5, Theorem 4.4.1, Lemmas 4.4.3–4.4.5 and Corollary 4.4.1.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ`, the index $i=1,\dots,m$ is `Fin m`, and positive semidefiniteness is Mathlib's `Matrix.PosSemidef` (which includes symmetry); $X\succeq Y$ is `(X - Y).PosSemidef`. $\|z\|_\infty\le\rho$ is written coordinatewise, $|z_i|\le\rho$ for all $i$. The eigenvalue vector `eigVec` is Mathlib's `IsHermitian.eigenvalues` (unordered; only $\|\lambda\|_1$ and $\|\lambda\|_\infty$ are used) with junk value $0$ on non-symmetric input, which no statement uses. The integral in $\theta$ is a Lebesgue integral over `Fin k → ℝ`, and the minimum is the real infimum `sInf` of the image of the unit $\ell_1$-sphere: for $k\ge1$ this set is nonempty, compact, the integral is continuous and nonnegative in $\alpha$, so the infimum is the attained minimum of the book. The book defines $\theta(k)$ only for $k\ge1$; for $k=0$ the formula returns $1/0=0$ in Lean, a value no statement of the mission relies on. The two radii are `sSup`s in `EReal`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 189 (4.4.35) and Matrix Cube, p. 190 (S_ρ) and p_n, p. 191 (4.4.38), p. 194 (4.4.45)

import Mathlib

open Matrix

namespace ModernConvex.MatrixCube

/-- The vector of eigenvalues `λ(X)` of a symmetric `n × n` real matrix (Ben-Tal–Nemirovski,
p. 147), counted with multiplicity, in Mathlib's order (`IsHermitian.eigenvalues`). Only
order-independent quantities of it (`‖λ(X)‖₁`, `‖λ(X)‖_∞`) are used. A non-symmetric input gets
the junk value `0`; every statement of the mission applies `eigVec` to symmetric matrices only. -/
noncomputable def eigVec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  if h : X.IsHermitian then h.eigenvalues else 0

/-- `‖λ(X)‖₁ = ∑ᵢ |λᵢ(X)|`, the sum of the absolute values of the eigenvalues of a symmetric
matrix `X`. -/
noncomputable def eigL1 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, |eigVec X i|

/-- The standard Gaussian density on `ℝᵏ` (p. 190):
`p_k(u) = (2π)^{−k/2} exp{−uᵀu/2}`. -/
noncomputable def gaussDensity (k : ℕ) (u : Fin k → ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(k : ℝ) / 2) * Real.exp (-(∑ i, u i ^ 2) / 2)

/-- The integral `∫ |α₁u₁² + ⋯ + α_k u_k²| p_k(u) du` over `ℝᵏ` (Lebesgue measure) appearing in
(4.4.38), p. 191. -/
noncomputable def thetaIntegral (k : ℕ) (α : Fin k → ℝ) : ℝ :=
  ∫ u : Fin k → ℝ, |∑ i, α i * u i ^ 2| * gaussDensity k u

/-- The function `θ` of (4.4.38), p. 191:
`θ(k) = 1 / min { ∫ |α₁u₁² + ⋯ + α_k u_k²| p_k(u) du | α ∈ ℝᵏ, ‖α‖₁ = 1 }`.
The book defines `θ(k)` for `k ≥ 1`, where the set `{α : ‖α‖₁ = 1}` is a nonempty compact set,
the integral is a continuous function of `α`, nonnegative, so the real infimum below is the
attained minimum. For `k = 0` the set is empty and the formula gives the junk value
`1 / sInf ∅ = 1 / 0 = 0`; no statement of the mission relies on `θ(0)`. -/
noncomputable def theta (k : ℕ) : ℝ :=
  1 / sInf (thetaIntegral k '' {α : Fin k → ℝ | ∑ i, |α i| = 1})

/-- The matrix cube (4.4.35), p. 189:
`𝒜_ρ = { A₀ + ∑_{i=1}^m zᵢAᵢ | ‖z‖_∞ ≤ ρ }`,
the image of the cube `{z ∈ ℝᵐ | ‖z‖_∞ ≤ ρ}` under `z ↦ A₀ + ∑ᵢ zᵢAᵢ`. The book's index
`i = 1, …, m` is `i : Fin m`. -/
def matrixCube {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {B | ∃ z : Fin m → ℝ, (∀ i, |z i| ≤ ρ) ∧ B = A₀ + ∑ i, z i • A i}

/-- The inclusion `𝒜_ρ ⊂ Sⁿ₊`: every matrix of the cube is positive semidefinite. -/
def CubeInPSD {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ) : Prop :=
  ∀ B ∈ matrixCube A₀ A ρ, B.PosSemidef

/-- `X¹, …, Xᵐ ∈ Sⁿ` solve the system of LMIs `(S_ρ)`, p. 190:
`(a) Xⁱ ⪰ ρAᵢ, Xⁱ ⪰ −ρAᵢ, i = 1, …, m`, `(b) ∑_{i=1}^m Xⁱ ⪯ A₀`. -/
def IsSystemSolution {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (X : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Prop :=
  (∀ i, (X i).IsHermitian) ∧
    (∀ i, (X i - ρ • A i).PosSemidef ∧ (X i - (-ρ) • A i).PosSemidef) ∧
    (A₀ - ∑ i, X i).PosSemidef

/-- The system of LMIs `(S_ρ)` is solvable. -/
def SystemSolvable {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) : Prop :=
  ∃ X : Fin m → Matrix (Fin n) (Fin n) ℝ, IsSystemSolution A₀ A ρ X

/-- `R[A₁, …, A_m : A₀]` (p. 189): the largest `ρ ≥ 0` with `𝒜_ρ ⊂ Sⁿ₊`, as a supremum in
`[−∞, +∞]`. The set always contains `ρ = 0` when `A₀ ⪰ 0`, and the value is `+∞` exactly when
the inclusion holds for every `ρ` (e.g. all `Aᵢ = 0`). -/
noncomputable def cubeRadius {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sSup {r : EReal | ∃ ρ : ℝ, r = ρ ∧ 0 ≤ ρ ∧ CubeInPSD A₀ A ρ}

/-- `ρ[A₁, …, A_m : A₀]`, the optimal value of the semidefinite problem (4.4.45), p. 194:
`max_{ρ, Xⁱ} { ρ | Xⁱ ⪰ ρAᵢ, Xⁱ ⪰ −ρAᵢ, i = 1, …, m, ∑ᵢ Xⁱ ⪯ A₀ }`,
as a supremum in `[−∞, +∞]` (`+∞` when the problem is unbounded). -/
noncomputable def sdpBound {n m : ℕ} (A₀ : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : EReal :=
  sSup {r : EReal | ∃ ρ : ℝ, r = ρ ∧ SystemSolvable A₀ A ρ}

end ModernConvex.MatrixCube


