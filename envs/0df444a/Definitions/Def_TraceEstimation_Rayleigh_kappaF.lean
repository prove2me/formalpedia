-- Prove2me | Definitions.Def_TraceEstimation_Rayleigh_kappaF
-- name    : TraceEstimation_Rayleigh_kappaF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:18:36.883323+00:00
-- url     : https://prove2.me/theorems/38a47324-3efe-4cc8-a7f0-4f8bf178a66a
-- title:
--   Theorem 6.1 — $\kappa_f(A)$, the ratio of the largest to the smallest nonzero eigenvalue; $\lambda_n$, the largest eigenvalue
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a symmetric matrix with eigenvalues $\lambda_1, \ldots, \lambda_n$ (with multiplicity). This file defines three objects used in Theorem 6.1 and its proof.
--
--   1. The set of **nonzero eigenvalues** $\Lambda^{\ne 0}(A) = \{\lambda_i : \lambda_i \ne 0\}$, a finite set of reals that is empty exactly when $A = 0$.
--   2. The **largest eigenvalue** $\lambda_n = \max_i \lambda_i$ (the page orders the eigenvalues increasingly, so the largest is $\lambda_n$).
--   3. The quantity
--   $$\kappa_f(A) = \frac{\max \Lambda^{\ne 0}(A)}{\min \Lambda^{\ne 0}(A)},$$
--   "the ratio between the largest and smallest nonzero eigenvalue of $A$". For a positive semi-definite $A \ne 0$ it is the condition number of $A$ restricted to its range, and $\kappa_f(A) \ge 1$.
--
--   The sample bound of Theorem 6.1 grows with $\kappa_f^2(A)$, which is why that bound is useful only for well-conditioned matrices.
--
--   **Formalization Note** The functions take the symmetry proof `hA : A.IsHermitian` and use Mathlib's `hA.eigenvalues : Fin n → ℝ`. Maxima and minima are `Finset.max'`/`min'`/`sup'` of nonempty finite sets, not `⨆`/`⨅`. For $A = 0$ (no nonzero eigenvalue) `kappaF` returns the placeholder $0$, and for $n = 0$ `lambdaMax` returns $0$; every statement of the mission that uses them assumes $A \ne 0$ (which forces $n \ge 1$).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:10, Theorem 6.1 (definition of κ_f) and its proof (λ_n)

import Mathlib

namespace TraceEstimation.Rayleigh

open Matrix

/-- The finite set of nonzero eigenvalues of a symmetric real matrix `A` (the values
`λ` with `λ ≠ 0` among its eigenvalues `λ_1, …, λ_n`). It is empty exactly when `A = 0`. -/
noncomputable def nonzeroEigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Finset ℝ :=
  (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).image hA.eigenvalues

/-- The largest eigenvalue `λ_n` of a symmetric real matrix `A` (Avron–Toledo, proof of
Theorem 6.1, p. 8:10). For `n = 0` (no eigenvalues) the value is the placeholder `0`. -/
noncomputable def lambdaMax {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then Finset.univ.sup' h hA.eigenvalues else 0

/-- `κ_f(A)`, "the ratio between the largest and smallest nonzero eigenvalue of `A`"
(Avron–Toledo, Theorem 6.1, p. 8:10). The quotient of the maximum by the minimum of the finite
set of nonzero eigenvalues. For `A = 0` that set is empty and the value is the placeholder `0`;
every statement using `kappaF` assumes `A ≠ 0`. -/
noncomputable def kappaF {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  if h : (nonzeroEigenvalues hA).Nonempty then
    (nonzeroEigenvalues hA).max' h / (nonzeroEigenvalues hA).min' h
  else 0

end TraceEstimation.Rayleigh


