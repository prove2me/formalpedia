-- Prove2me | Definitions.Def_SpencerEight_IsSymmContraction
-- name    : SpencerEight_IsSymmContraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:17.77519+00:00
-- url     : https://prove2.me/theorems/e09f93a7-b500-412d-9849-ce0bff948c10
-- title:
--   Symmetric contraction
-- statement:
--   A **symmetric contraction** is a real symmetric matrix $A$ with $\|A\|\le 1$, where $\|\cdot\|$ is the operator norm.
--
--   The inputs of the Matrix Spencer problem are symmetric contractions, and the congruences of the signing schedule preserve the class.
--
--   **Formalization Note** The norm is the L2 operator norm of Mathlib, opened from `Matrix.Norms.L2Operator`.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21)

import Mathlib
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- A symmetric contraction (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21)): a symmetric matrix `A` with `‖A‖ ≤ 1`, where the unadorned norm is the operator norm.

**Formalization Note** `‖·‖` is Mathlib's L2 operator norm on `Matrix d d ℝ`. -/
def IsSymmContraction {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℝ) : Prop :=
  A.IsSymm ∧ ‖A‖ ≤ 1

end SpencerEight


