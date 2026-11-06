-- Prove2me | Definitions.Def_BlockBochner_lamMax
-- name    : BlockBochner_lamMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:27.651709+00:00
-- url     : https://prove2.me/theorems/893c6217-7931-42a1-b310-1dc3a74a7af8
-- title:
--   Largest eigenvalue $\lambda_{\max}(A)$
-- statement:
--   For a real symmetric matrix $A$, $\lambda_{\max}(A)$ is its largest eigenvalue.
--
--   **Formalization Note** The supremum of the real spectrum of $A$; for a symmetric matrix on a nonempty index set the spectrum is the finite nonempty set of eigenvalues.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4

import Mathlib

namespace BlockBochner

/-- **Largest eigenvalue `λ_max(A)` of a real symmetric matrix.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4 (`λ_max(A) < 1`,
`λ_max(H)`).

**Formalization Note** The supremum of the real spectrum of `A` in the algebra of `n × n` real
matrices. For a symmetric matrix on a nonempty index type the spectrum is the finite nonempty set of
its eigenvalues, so this is the largest eigenvalue. It is only applied to symmetric matrices. -/
noncomputable def lamMax {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : ℝ :=
  sSup (spectrum ℝ A)

end BlockBochner


