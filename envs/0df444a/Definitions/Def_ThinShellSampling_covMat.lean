-- Prove2me | Definitions.Def_ThinShellSampling_covMat
-- name    : ThinShellSampling_covMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:28.525122+00:00
-- url     : https://prove2.me/theorems/0dd09b76-4d8f-464a-b848-e8f413ab1f14
-- title:
--   Barycenter $m$, covariance $\Sigma$, $R^2$, $L$, $\Lambda$, $M^{1/2}$, sorted eigenvalues
-- statement:
--   For a probability measure $\pi$ on $\mathbb R^n$:
--
--   1. the **barycenter** $m=\mathbb E_\pi X$ and **covariance matrix** $\Sigma=\operatorname{cov}\pi$, $\Sigma_{ij}=\int(x_i-m_i)(x_j-m_j)\,d\pi$;
--   2. the **second-moment matrix** $\mathbb E_\pi[XX^{\mathsf T}]=\Sigma+mm^{\mathsf T}$;
--   3. $R^2=\mathbb E_\pi\|X\|^2$, $L=\|\mathbb E_\pi[XX^{\mathsf T}]\|_{\mathrm{op}}$ and $\Lambda=\|\Sigma\|_{\mathrm{op}}$, where $\|\cdot\|_{\mathrm{op}}$ is the operator norm for the Euclidean norm.
--
--   Also defined: the positive semidefinite square root $M^{1/2}$ of a matrix $M\succeq0$, and the eigenvalues $\lambda_1\ge\dots\ge\lambda_n$ of a symmetric matrix in decreasing order.
--
--   These are the parameters of the complexity bound of Theorem 1.7 and of the thin-shell estimate (Theorem 1.4); note $\Lambda\le L$ and $\operatorname{tr}\Sigma\le R^2$.
--
--   **Formalization Note** Moments are Bochner integrals; every measure they are applied to has finite second moment (logconcave measures and their tilts, or an explicit hypothesis). $M^{1/2}$ is Mathlib's `CFC.sqrt` for the Loewner order; sorted eigenvalues are Mathlib's antitone `eigenvalues₀` of the symmetric part $(A+A^{\mathsf T})/2$, which is $A$ for symmetric $A$.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6); §1.3, p.12 (PDF p.14); §4.1, p.25 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped MatrixOrder

/-- **Barycenter** `m = E_μ X` of a measure on `ℝⁿ`.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6): "we denote the barycenter by `m := E_π X`".

**Formalization Note.** Bochner integral; every measure to which it is applied in this mission has
a finite first moment (logconcave measures and their tilts, or an explicit `MemLp id 2` hypothesis). -/
noncomputable def mean {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  ∫ x, x ∂μ

/-- **Second-moment matrix** `E_μ[XXᵀ]`, entrywise `∫ xᵢ xⱼ dμ`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6):
"`L := ‖E_π[XXᵀ]‖_op = ‖Σ + mmᵀ‖_op`". -/
noncomputable def secondMomentMat {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, x i * x j ∂μ

/-- **Covariance matrix** `Σ = cov μ`, entrywise `∫ (xᵢ − mᵢ)(xⱼ − mⱼ) dμ` with `m` the barycenter.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6): "the
covariance matrix by `Σ := cov_π X = cov π`"; §4.1, p.25 (PDF p.27): `B_s = cov_s X`. -/
noncomputable def covMat {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, (x i - mean μ i) * (x j - mean μ j) ∂μ

/-- **Operator norm** `‖A‖_op` of a real `n × n` matrix, for the Euclidean norm on `ℝⁿ`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.3, p.12 (PDF p.14): "For a
positive semidefinite matrix `Σ`, `‖Σ‖_op` denotes the operator norm of `Σ`." -/
noncomputable def opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖

/-- **`R² = E_μ‖X‖²`**, the second moment of the norm.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.4 (PDF p.6):
"`R² = E_π[‖X‖²]`". `R` itself is `Real.sqrt (rsq μ)`. -/
noncomputable def rsq {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ x, ‖x‖ ^ 2 ∂μ

/-- **`L = ‖E_μ[XXᵀ]‖_op`** (Kook, Vempala, STOC 2027 submission, manuscript sha256 25a041a9…,
§1.1, p.4 = PDF p.6). -/
noncomputable def Lmom {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ :=
  opNorm (secondMomentMat μ)

/-- **`Λ = ‖cov μ‖_op`** (Kook, Vempala, STOC 2027 submission, manuscript sha256 25a041a9…,
§1.1, p.4 = PDF p.6: "its operator norm by `Λ := ‖cov π‖_op`"). -/
noncomputable def Lam {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) : ℝ :=
  opNorm (covMat μ)

/-- **Matrix square root** `M^{1/2}` of a positive semidefinite matrix (Kook, Vempala, STOC 2027
submission, manuscript sha256 25a041a9…, §4, pp.24–25 = PDF pp.26–27).

**Formalization Note.** Mathlib's continuous-functional-calculus square root `CFC.sqrt` for the
Loewner order on matrices; for `M ⪰ 0` it is the unique positive semidefinite square root. Only
positive semidefinite `M` are used. -/
noncomputable def msqrt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  CFC.sqrt M

/-- The symmetric part `(A + Aᵀ)/2` of a real square matrix is Hermitian (structural lemma). -/
theorem isHermitian_symPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ((1 / 2 : ℝ) • (A + A.transpose)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply, add_comm]
  ring

/-- **Eigenvalues in decreasing order** `λ₁ ≥ ⋯ ≥ λₙ` of a real symmetric matrix.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §4.1, p.25 (PDF p.27):
"each eigenvalue `(λ_i(s))_{i∈[n]}` of `M_s`".

**Formalization Note.** Defined for every real square matrix as the eigenvalues of its symmetric
part `(A + Aᵀ)/2`, sorted decreasingly (Mathlib's `eigenvalues₀` is antitone); for symmetric `A`
these are the eigenvalues of `A`. Lemma 4.5 uses it only to describe the eigenvalue list of a
matrix up to permutation. -/
noncomputable def sortedEig {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun i => (isHermitian_symPart A).eigenvalues₀ (Fin.cast (by simp) i)

end ThinShellSampling


