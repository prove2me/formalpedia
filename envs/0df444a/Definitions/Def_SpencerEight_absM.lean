-- Prove2me | Definitions.Def_SpencerEight_absM
-- name    : SpencerEight_absM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:35.617546+00:00
-- url     : https://prove2.me/theorems/2617ec2f-9540-4176-95b5-cf08d3adc85e
-- title:
--   Matrix absolute value $|M|$
-- statement:
--   For a real symmetric matrix $M=U\operatorname{diag}(\lambda_i)U^\top$, the matrix absolute value is $|M|=U\operatorname{diag}(|\lambda_i|)U^\top$. It agrees with $(M^\top M)^{1/2}$.
--
--   **Formalization Note** Mathlib's continuous functional calculus `cfc`, which is the eigenvalue formula on a symmetric matrix and returns $0$ on a non-symmetric one. It is used on symmetric matrices only.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21)

import Mathlib

namespace SpencerEight

/-- The matrix absolute value `|M| = f(M)`, `f(x) = |x|` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 4.1, p.21 (PDF p.21)).

**Formalization Note** Mathlib's `cfc`, which on a real symmetric matrix is `U diag(f(λ_i)) Uᵀ`, the book's functional calculus. `cfc` returns `0` on a non-symmetric matrix; this mission applies it to symmetric matrices only. -/
noncomputable def absM {d : Type*} [Fintype d] [DecidableEq d] (M : Matrix d d ℝ) : Matrix d d ℝ :=
  cfc (fun x : ℝ => |x|) M

end SpencerEight


