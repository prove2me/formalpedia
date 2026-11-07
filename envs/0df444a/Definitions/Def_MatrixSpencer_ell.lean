-- Prove2me | Definitions.Def_MatrixSpencer_ell
-- name    : MatrixSpencer_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:58.252342+00:00
-- url     : https://prove2.me/theorems/71931c64-58c5-4197-9121-9432193902da
-- title:
--   The log-barrier $\ell(x)=-\log(1-x^2)$
-- statement:
--   The scalar log-barrier
--   $$\ell(x)=-\log(1-x^2),\qquad |x|<1.$$
--   It is the first ingredient of the spectral potential $v$.
--
--   **Formalization Note** It is read on $(-1,1)$ only.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8

import Mathlib

namespace MatrixSpencer

/-- **The log-barrier `ℓ(x) = −log(1 − x²)`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8.

**Formalization Note.** It is read on `(−1, 1)` only: `weight` is `0` when the matrix leaves the
open unit ball, and all derivative statements are at points of `(−1, 1)`. -/
noncomputable def ell (x : ℝ) : ℝ := -Real.log (1 - x ^ 2)

end MatrixSpencer


