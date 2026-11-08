-- Prove2me | Definitions.Def_SpencerEight_sqrtM
-- name    : SpencerEight_sqrtM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:38.927401+00:00
-- url     : https://prove2.me/theorems/eb497d30-8016-424b-b8db-8648ab6054e4
-- title:
--   Matrix square root $T^{1/2}$
-- statement:
--   For a positive semidefinite matrix $T=U\operatorname{diag}(\lambda_i)U^\top$, the square root is $T^{1/2}=U\operatorname{diag}(\sqrt{\lambda_i})U^\top$.
--
--   **Formalization Note** `cfc Real.sqrt T`, used on positive semidefinite matrices only.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21)

import Mathlib

namespace SpencerEight

/-- The matrix square root `T^{1/2}` of a positive semidefinite matrix (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21): functional calculus).

**Formalization Note** `cfc Real.sqrt T`; every use has `T` positive semidefinite. -/
noncomputable def sqrtM {d : Type*} [Fintype d] [DecidableEq d] (T : Matrix d d ℝ) : Matrix d d ℝ :=
  cfc Real.sqrt T

end SpencerEight


