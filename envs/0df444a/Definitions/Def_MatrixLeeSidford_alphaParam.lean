-- Prove2me | Definitions.Def_MatrixLeeSidford_alphaParam
-- name    : MatrixLeeSidford_alphaParam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:28.307602+00:00
-- url     : https://prove2.me/theorems/0b32b380-8c17-4503-bfcb-b1795e5226cb
-- title:
--   Scaling $\alpha=10^6s^2$
-- statement:
--   The scaling of the barrier is $\alpha=10^6s^2$, so that $\alpha^{1/2}=1000s$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29

import Mathlib

namespace MatrixLeeSidford

/-- The scaling `α := 10⁶ s²` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29). -/
def alphaParam (s : ℕ) : ℝ :=
  10 ^ 6 * (s : ℝ) ^ 2

end MatrixLeeSidford


