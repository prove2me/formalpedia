-- Prove2me | Definitions.Def_BlockBochner_lamMin
-- name    : BlockBochner_lamMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:32.585807+00:00
-- url     : https://prove2.me/theorems/2404a63c-3808-4e0b-a47b-f7c5858ec666
-- title:
--   Smallest eigenvalue $\lambda_{\min}(A)$
-- statement:
--   For a real symmetric matrix $A$, $\lambda_{\min}(A)$ is its smallest eigenvalue.
--
--   **Formalization Note** The infimum of the real spectrum of $A$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 21, p.22; Sec. 3.3, p.23

import Mathlib

namespace BlockBochner

/-- **Smallest eigenvalue `λ_min(A)` of a real symmetric matrix.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 21, p.22
(`α = λ_min(D^{−1/2} C D^{−1/2})`) and Sec. 3.3, p.23 (`λ_min(M)`).

**Formalization Note** The infimum of the real spectrum of `A`; for a symmetric matrix on a nonempty
index type this is its smallest eigenvalue. It is only applied to symmetric matrices. -/
noncomputable def lamMin {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) : ℝ :=
  sInf (spectrum ℝ A)

end BlockBochner


