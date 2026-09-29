-- Prove2me | Definitions.Def_CaiCandesShen_Convergence_Problems
-- name    : CaiCandesShen_Convergence_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:12:18.543544+00:00
-- url     : https://prove2.me/theorems/7e894330-6829-4735-b5b6-95fc1fe0b889
-- title:
--   Problems (2.8) and (3.1), linear maps $\mathcal A$, their adjoint and spectral norm, sampling operators
-- statement:
--   Fix $\tau$, an index set $\Omega$ and a matrix $M\in\mathbb R^{n_1\times n_2}$.
--
--   1. **Problem (2.8).** $X^\star$ solves (2.8) if it is feasible and optimal for
--   $$\text{minimize } \tau\|X\|_*+\tfrac12\|X\|_F^2\quad\text{subject to } P_\Omega(X)=P_\Omega(M).$$
--   2. **Linear maps into $\mathbb R^m$.** A linear map $\mathcal A:\mathbb R^{n_1\times n_2}\to\mathbb R^m$ is given by matrices $A_1,\dots,A_m$ through $\mathcal A(X)_i=\langle A_i, X\rangle$; its adjoint is $\mathcal A^*(y)=\sum_i y_iA_i$, and its spectral norm is
--   $$\|\mathcal A\|_2 := \sup\{\|\mathcal A(X)\|_{\ell_2} : \|X\|_F=1\}.$$
--   3. **Problem (3.1).** For $b\in\mathbb R^m$, $X^\star$ solves (3.1) if it is feasible and optimal for
--   $$\text{minimize } f_\tau(X)\quad\text{subject to } \mathcal A(X)=b.$$
--   4. **Sampling operator.** For an enumeration $\omega:\{1,\dots,m\}\to\{1,\dots,n_1\}\times\{1,\dots,n_2\}$, the sampling operator extracts the entries $\mathcal A(X)_i = X_{\omega(i)}$; it is given by the matrix units $A_i = e_{\omega(i)}$.
--
--   Problem (2.8) is the proximal problem to which the SVT iterates converge; (3.1) is its generalization to arbitrary linear equality constraints.
--
--   **Formalization Note** "Solves" means: satisfies the constraint and has objective value at most that of every feasible matrix. The spectral norm is a real `sSup` over the Frobenius unit sphere; for $n_1n_2\ge1$ that set is nonempty and bounded, and for $n_1n_2=0$ the sphere is empty and the value is $0$, which is the correct norm of the zero map.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1961 Eq. (2.8); p. 1964 §3.1 Eq. (3.1) and sampling operator; p. 1968 §4.2 (definition of ‖A‖₂)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

open Matrix

/-- `Xs` solves problem (2.8), p. 1961: minimize `τ‖X‖_* + ½‖X‖_F²` subject to
`P_Ω(X) = P_Ω(M)`. -/
def IsSol28 {n₁ n₂ : ℕ} (τ : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) (M Xs : Mat n₁ n₂) : Prop :=
  projΩ Ω Xs = projΩ Ω M ∧ ∀ X, projΩ Ω X = projΩ Ω M → fτ τ Xs ≤ fτ τ X

/-- The linear map `𝒜 : ℝ^{n₁×n₂} → ℝ^m` given by the matrices `Aop i`:
`𝒜(X)_i = ⟨Aop i, X⟩` (every linear map into `ℝ^m` has this form). -/
def applyA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) (X : Mat n₁ n₂) : Fin m → ℝ :=
  fun i => frobInner (Aop i) X

/-- The adjoint `𝒜*(y) = ∑_i y_i Aop i` of `applyA Aop`. -/
def adjA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) (y : Fin m → ℝ) : Mat n₁ n₂ :=
  ∑ i, y i • Aop i

/-- The spectral norm `‖𝒜‖₂ := sup{‖𝒜(X)‖_ℓ₂ : ‖X‖_F = 1}` of the linear map `𝒜` (§4.2,
p. 1968). When `n₁ n₂ = 0` the unit sphere is empty and the value is `0`. -/
noncomputable def opNormA {n₁ n₂ m : ℕ} (Aop : Fin m → Mat n₁ n₂) : ℝ :=
  sSup ((fun X => Real.sqrt (∑ i, applyA Aop X i ^ 2)) '' {X : Mat n₁ n₂ | frobNorm X = 1})

/-- `Xs` solves problem (3.1), p. 1964: minimize `f_τ(X)` subject to `𝒜(X) = b`. -/
def IsSol31 {n₁ n₂ m : ℕ} (τ : ℝ) (Aop : Fin m → Mat n₁ n₂) (b : Fin m → ℝ) (Xs : Mat n₁ n₂) :
    Prop :=
  applyA Aop Xs = b ∧ ∀ X, applyA Aop X = b → fτ τ Xs ≤ fτ τ X

/-- The sampling operator extracting the `m` entries with indices `ω 0, …, ω (m − 1)`:
`𝒜(X)_i = X_{ω i}`, given by the matrix units `Aop i = e_{ω i}` (§3.1, p. 1964). -/
def samplingOp {n₁ n₂ m : ℕ} (ω : Fin m → Fin n₁ × Fin n₂) : Fin m → Mat n₁ n₂ :=
  fun i => Matrix.single (ω i).1 (ω i).2 1

end CaiCandesShen.Convergence


