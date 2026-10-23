-- Prove2me | Definitions.Def_BSPConvex_CMM_Model
-- name    : BSPConvex_CMM_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:05.023987+00:00
-- url     : https://prove2.me/theorems/f9b40cee-d99a-4369-9871-42133759f93e
-- title:
--   §4.1, pp. 8–9, 28 — simplex Δm and int(Δm), S(x) = Diag(x) − xxᵀ, T(x) = Σ^{1/2}S(x)Σ^{1/2}, f, ∇f, the BSP-CMM profit π(q) of (6), g(q) = −qᵀ∇f(q)
-- statement:
--   This file fixes the objects of the bundle size pricing problem under the cross moment model (CMM) of Li, Sun and Teo.
--
--   A firm offers $m$ bundle sizes. Let $\Sigma\in\mathbb R^{m\times m}$ be the covariance matrix of the customer's bundle valuations, $\omega,c\in\mathbb R^m$ the mean valuations and the bundle costs, and $e$ the all-ones vector. For a positive semidefinite matrix $A$, $A^{1/2}$ is its unique positive semidefinite square root.
--
--   1. The simplex and its interior:
--   $$\Delta_m=\{x\in\mathbb R^m_+ : e^\top x\le 1\},\qquad \operatorname{int}(\Delta_m)=\{x\in\mathbb R^m : e^\top x<1,\ x>0\}.$$
--   2. The matrices
--   $$S(x)=\operatorname{Diag}(x)-xx^\top,\qquad T(x)=\Sigma^{1/2}S(x)\Sigma^{1/2},$$
--   where $\operatorname{Diag}(x)$ is the diagonal matrix with diagonal $x$.
--   3. The function $f(x)=\operatorname{tr}\big((\Sigma^{1/2}S(x)\Sigma^{1/2})^{1/2}\big)=\operatorname{tr}\big(T(x)^{1/2}\big)$.
--   4. The matrix $M(q)=\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}$ and the vector given by the displayed gradient formula of p. 9,
--   $$\nabla f(q)=\tfrac12\operatorname{diag}(M(q))-M(q)\,q,$$
--   where $\operatorname{diag}(X)$ is the vector of diagonal entries of $X$.
--   5. The objective of Problem (6), the expected profit as a function of the choice probabilities $q$:
--   $$\pi(q)=q^\top(\omega-c)+\tfrac12 q^\top\operatorname{diag}\big(\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}\big)-q^\top\Sigma^{1/2}(T(q))^{-1/2}\Sigma^{1/2}q.$$
--   6. The auxiliary function of the proof of Theorem 2, $g(q)=-q^\top\nabla f(q)$.
--   7. The bordered matrix $\begin{pmatrix} a & u^\top\\ v & C\end{pmatrix}$ with a scalar $a$, vectors $u,v\in\mathbb R^m$ and an $m\times m$ block $C$, used in the epigraph representation of p. 28.
--
--   In the paper, $\pi$ is the profit of the bundle size pricing problem because, by Theorem 1 and Lemmas 1–2, every choice-probability vector $q\in\operatorname{int}(\Delta_m)$ is induced by the unique price $p=\omega+\nabla f(q)$; here $\pi$ is the explicit function (6).
--
--   **Formalization Note** Vectors are functions `Fin m → ℝ` and matrices are real `Matrix (Fin m) (Fin m) ℝ`; $\Sigma$ is named `Sig`. $A^{1/2}$ is Mathlib's `CFC.sqrt` under `open scoped MatrixOrder` (the Loewner order on real matrices), which is the positive semidefinite square root on positive semidefinite input. $(T(q))^{-1/2}$ is `(CFC.sqrt (T q))⁻¹`, the matrix inverse, which Lean sets to $0$ when $T(q)$ is singular; this happens on the boundary of $\Delta_m$, so every statement involving $M$, $\nabla f$, $\pi$ or $g$ is made on $\operatorname{int}(\Delta_m)$. $\nabla f$ (`gradF`) is defined by the displayed formula; that it is the gradient of $f$ is a separate theorem. $\pi$ is written literally as in (6), not through $\nabla f$.
-- source:
--   Li, Sun & Teo, Convex Optimization for Bundle Size Pricing Problem, SSRN 3426933 (version of May 8, 2021), pp. 8–9, §4.1, Theorem 1 (definitions of S(x), A^{1/2}, Δm), int(Δm) and f (p. 8), ∇f and T(q) (p. 9), Equation (6) (p. 9); p. 28, proof of Theorem 2 (g and the bordered matrix)

import Mathlib

open Matrix
open scoped MatrixOrder

namespace BSPConvex.CMM

/-- The simplex `Δm = {x ∈ ℝ^m_+ | eᵀx ≤ 1}` (p. 8). -/
def simplex (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The interior `int(Δm) = {x ∈ ℝ^m : eᵀx < 1, x > 0}` (p. 8). -/
def intSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}

/-- `S(x) = Diag(x) − x xᵀ` (p. 8). -/
noncomputable def Smat {m : ℕ} (x : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal x - Matrix.vecMulVec x x

/-- `T(x) = Σ^{1/2} S(x) Σ^{1/2}` (p. 9), with `Σ^{1/2}` the positive semidefinite square root. -/
noncomputable def Tmat {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt Sig * Smat x * CFC.sqrt Sig

/-- `f(x) = tr((Σ^{1/2} S(x) Σ^{1/2})^{1/2})` (p. 8). -/
noncomputable def fCMM {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) : ℝ :=
  Matrix.trace (CFC.sqrt (Tmat Sig x))

/-- `M(q) = Σ^{1/2} (T(q))^{−1/2} Σ^{1/2}`, the matrix occurring in `∇f` and in (6) (p. 9). -/
noncomputable def Mmat {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt Sig * (CFC.sqrt (Tmat Sig q))⁻¹ * CFC.sqrt Sig

/-- The displayed formula `∇f(q) = ½ diag(M(q)) − M(q) q` (p. 9). -/
noncomputable def gradF {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) : Fin m → ℝ :=
  (1 / 2 : ℝ) • Matrix.diag (Mmat Sig q) - Mmat Sig q *ᵥ q

/-- The BSP-CMM profit of (6) (p. 9):
`π(q) = qᵀ(ω − c) + ½ qᵀ diag(Σ^{1/2}(T(q))^{−1/2}Σ^{1/2}) − qᵀ Σ^{1/2}(T(q))^{−1/2}Σ^{1/2} q`. -/
noncomputable def profit {m : ℕ} (ω c : Fin m → ℝ) (Sig : Matrix (Fin m) (Fin m) ℝ)
    (q : Fin m → ℝ) : ℝ :=
  q ⬝ᵥ (ω - c) + (1 / 2 : ℝ) * (q ⬝ᵥ Matrix.diag (Mmat Sig q)) - q ⬝ᵥ (Mmat Sig q *ᵥ q)

/-- `g(q) = −qᵀ∇f(q)` (p. 28). -/
noncomputable def gFun {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) : ℝ :=
  -(q ⬝ᵥ gradF Sig q)

/-- The bordered matrix `( a  uᵀ ; v  C )` on the index type `Unit ⊕ Fin m`: scalar `a` in the
top-left corner, row vector `u` in the top-right block, column vector `v` in the bottom-left block,
and the `m × m` block `C` (p. 28). -/
def bord {m : ℕ} (a : ℝ) (u v : Fin m → ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (Matrix.of fun (_ _ : Unit) => a) (Matrix.of fun (_ : Unit) j => u j)
    (Matrix.of fun i (_ : Unit) => v i) C

end BSPConvex.CMM


