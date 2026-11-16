-- Prove2me | Definitions.Def_CtxSearchTSR_Supplement_Moments
-- name    : CtxSearchTSR_Supplement_Moments
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:19:44.182889+00:00
-- url     : https://prove2.me/theorems/0e939d9a-31c0-4f39-8585-9b0eefa52d96
-- title:
--   Mean, covariance, $\operatorname{Tr}\sqrt{\Sigma}$ and standard deviation of a distribution
-- statement:
--   Let $\nu$ be a Borel measure on $\mathbb R^d$. It has **finite second moments** if every coordinate $z\mapsto z_i$ is square-integrable. Its **mean** and **covariance** are
--
--   $$\mu(\nu)_i=\int z_i\,d\nu(z),\qquad \operatorname{Cov}(\nu)_{ij}=\int (z_i-\mu_i)(z_j-\mu_j)\,d\nu(z).$$
--
--   For a symmetric matrix $\Sigma$ with eigenvalues $\lambda_1,\dots,\lambda_d$, the **trace-square-root potential** of the paper's definition (1) is
--
--   $$\Psi(\Sigma)=\operatorname{Tr}\sqrt{\Sigma}=\sum_{i=1}^d\sqrt{\lambda_i},$$
--
--   the trace of the positive-semidefinite square root when $\Sigma\succeq 0$. For a real function $f$ on a measure space, the **standard deviation** under $\nu$ is $\operatorname{sd}(f)=\big(\int (f-\int f\,d\nu)^2\,d\nu\big)^{1/2}$.
--
--   These are the quantities in which the Bayesian bounds of Theorems 2.1 and 3.2 are stated: $\operatorname{Tr}\sqrt{\Sigma_1}$ of the prior covariance, and the standard deviations entering the information measure $D(p)$.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` (product σ-algebra, which is the Borel σ-algebra). The integrals are Bochner integrals; every theorem using them assumes finite second moments. `trSqrt` is written as the sum of the square roots of the eigenvalues of a symmetric matrix (Mathlib's `IsHermitian.eigenvalues`) and is set to $0$ on a non-symmetric matrix, a case that never occurs for a covariance matrix (proved in the sanity file).
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), (1) p.3; §1.4 Notation p.7; §2.1 p.7; §3.1 p.11

import Mathlib

open MeasureTheory Matrix

namespace CtxSearchTSR.Supplement

/-!
# Moments of a distribution, the potential Ψ(Σ) = Tr √Σ, and standard deviations

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…):
Ψ(Σ) = Tr √Σ, (1), p.3; Cov(·) and sd(·), §1.4 Notation, p.7; "finite second moment", §2.1, p.7
and §3.1, p.11.

**Formalization Note.** Vectors of ℝ^d are `Fin d → ℝ` (product σ-algebra = Borel). The mean and
covariance are Bochner integrals; every theorem that uses them assumes finite second moments
(`HasFiniteSecondMoments`), under which every integral below is a genuine integral. `trSqrt Σ` is
Σᵢ √λᵢ over the eigenvalues λᵢ of a symmetric Σ, i.e. the trace of the positive-semidefinite square
root, which is the paper's definition (1); it is set to `0` for a non-symmetric matrix, a case that
never occurs because a covariance matrix is symmetric. `sd f ν` is the square root of the variance
of the real function `f` under `ν`.
-/

/-- Finite second moments: every coordinate is square-integrable under `ν`. -/
def HasFiniteSecondMoments {d : ℕ} (ν : Measure (Fin d → ℝ)) : Prop :=
  ∀ i : Fin d, MemLp (fun z : Fin d → ℝ => z i) 2 ν

/-- The mean vector µ(ν)ᵢ = ∫ zᵢ dν. -/
noncomputable def meanVec {d : ℕ} (ν : Measure (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => ∫ z, z i ∂ν

/-- The covariance matrix Cov(ν)ᵢⱼ = ∫ (zᵢ − µᵢ)(zⱼ − µⱼ) dν. -/
noncomputable def covMat {d : ℕ} (ν : Measure (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∫ z, (z i - meanVec ν i) * (z j - meanVec ν j) ∂ν

/-- The potential Ψ(Σ) = Tr √Σ = Σᵢ √λᵢ(Σ) of (1), for a symmetric matrix Σ (eigenvalues λᵢ). -/
noncomputable def trSqrt {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : S.IsHermitian then ∑ i, Real.sqrt (h.eigenvalues i) else 0

/-- The standard deviation sd(f) = (∫ (f − ∫ f dν)² dν)^{1/2} of a real function `f` under `ν`. -/
noncomputable def sd {α : Type*} [MeasurableSpace α] (f : α → ℝ) (ν : Measure α) : ℝ :=
  Real.sqrt (∫ q, (f q - ∫ q', f q' ∂ν) ^ 2 ∂ν)

end CtxSearchTSR.Supplement


