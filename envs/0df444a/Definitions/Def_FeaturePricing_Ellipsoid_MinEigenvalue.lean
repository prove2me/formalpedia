-- Prove2me | Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue
-- name    : FeaturePricing_Ellipsoid_MinEigenvalue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:22:20.110443+00:00
-- url     : https://prove2.me/theorems/94de953d-b329-4474-895d-f47a567f9f7f
-- title:
--   §5.1, pp. 13–14 — the smallest eigenvalue λ_d(A) of a real d × d matrix
-- statement:
--   For a real $d\times d$ matrix $A$ define
--   $$
--   \lambda_d(A) \;=\; \inf\,\{\mu\in\mathbb R : A-\mu I \text{ is singular}\},
--   $$
--   the infimum of the real spectrum of $A$.
--
--   The paper orders the eigenvalues of a symmetric matrix decreasingly, $\lambda_1(A)\ge\lambda_2(A)\ge\dots\ge\lambda_d(A)$, so $\lambda_d(A)$ is the smallest eigenvalue. For a symmetric $A$ and $d\ge 1$ the real spectrum is the finite, nonempty set of eigenvalues of $A$, so the infimum is a minimum and $\lambda_d(A)$ is exactly the paper's smallest eigenvalue. This quantity drives the regret analysis of EllipsoidPricing: Lemmas 2–4 and the proof of Lemma 1 bound it along the run of the algorithm.
--
--   **Formalization Note** The definition is `sInf (spectrum ℝ A)`. Mathlib's `Matrix.IsHermitian.eigenvalues` is not sorted, so the paper's index $d$ is not used as an index into it. Every statement using $\lambda_d$ assumes the matrix symmetric or positive definite and $d\ge1$; for $d=0$ the spectrum is empty and Lean returns the default value $0$.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), pp. 13–14, §5.1 (notation λ_1(A) ≥ … ≥ λ_d(A))

import Mathlib

namespace FeaturePricing.Ellipsoid

/-- **Cohen, Lobel, Paes Leme (2020), §5.1, pp. 13–14.** The smallest eigenvalue `λ_d(A)` of a
real `d × d` matrix `A`. The paper orders the eigenvalues of a symmetric matrix as
`λ₁(A) ≥ ⋯ ≥ λ_d(A)`, so `λ_d(A)` is the smallest one.

It is defined as the infimum of the real spectrum of `A` (the set of real `μ` with `A − μI`
singular). For a symmetric `A` with `d ≥ 1` that set is the finite, nonempty set of eigenvalues
of `A`, so the infimum is its minimum. Mathlib's `Matrix.IsHermitian.eigenvalues` is not sorted,
so it is not indexed here. Every statement using `lamMin` assumes the matrix symmetric (or
positive definite) and `d ≥ 1`; for `d = 0` the spectrum is empty and the value is the junk `0`. -/
noncomputable def lamMin {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf (spectrum ℝ A)

end FeaturePricing.Ellipsoid


