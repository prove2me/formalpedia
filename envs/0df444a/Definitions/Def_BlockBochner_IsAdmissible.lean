-- Prove2me | Definitions.Def_BlockBochner_IsAdmissible
-- name    : BlockBochner_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:16.458655+00:00
-- url     : https://prove2.me/theorems/d83dae8e-1d56-4351-8308-522b9988c14a
-- title:
--   Admissible interaction matrix
-- statement:
--   A $V\times V$ real matrix $A=(a_{uv})$ is admissible if it is symmetric, has non-negative entries and zero diagonal, and
--   $$\lambda_{\max}(A)<1 .$$
--   These are the hypotheses on $A$ in Theorem 3 and on $S$ in Theorem 21.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4; Theorem 21, p.22

import Mathlib
import Definitions.Def_BlockBochner_lamMax

namespace BlockBochner

/-- **Admissible interaction matrix.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4: "a `V × V` symmetric matrix `A` with
non-negative entries and zero diagonal such that `λ_max(A) < 1`"; the same conditions on `S` in
Theorem 21, p.22 ("maximum eigenvalue strictly less than 1"). -/
def IsAdmissible {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) : Prop :=
  A.IsSymm ∧ (∀ u v, 0 ≤ A u v) ∧ (∀ v, A v v = 0) ∧ lamMax A < 1

end BlockBochner


