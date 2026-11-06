-- Prove2me | Definitions.Def_BlockBochner_invSqrt
-- name    : BlockBochner_invSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:33.650656+00:00
-- url     : https://prove2.me/theorems/480e0c2e-6201-46fe-85dc-a93557ed6457
-- title:
--   Inverse square root $D^{-1/2}$
-- statement:
--   For a real symmetric positive definite matrix $D=U\,\mathrm{diag}(\lambda_i)\,U^\top$, $D^{-1/2}=U\,\mathrm{diag}(\lambda_i^{-1/2})\,U^\top$, the unique symmetric positive definite matrix with $D^{-1/2}DD^{-1/2}=I$.
--
--   **Formalization Note** Defined by the continuous functional calculus of symmetric matrices applied to $x\mapsto(\sqrt x)^{-1}$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4; Theorem 21, p.22

import Mathlib

namespace BlockBochner

/-- **Inverse square root `D^{−1/2}` of a positive definite matrix.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4
(`H = I − D^{−1/2} C D^{−1/2}`) and Theorem 21, p.22.

**Formalization Note** The continuous functional calculus of the real symmetric matrix `D` applied
to `x ↦ (√x)⁻¹`: `D^{−1/2} = U diag(λ_i^{−1/2}) Uᵀ` for an orthonormal eigenbasis `U`. For positive
definite `D` it satisfies `D^{−1/2} D D^{−1/2} = I` (checked in the verification file). -/
noncomputable def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (D : Matrix n n ℝ) : Matrix n n ℝ :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) D

end BlockBochner


