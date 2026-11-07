-- Prove2me | Definitions.Def_MatrixSpencer_tailR
-- name    : MatrixSpencer_tailR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:01.024713+00:00
-- url     : https://prove2.me/theorems/fcb574f4-bfe0-4b51-af3e-1c7e1a9cbd63
-- title:
--   The power-series tail $r_p(x)=\sum_{k\ge p}x^{2k}/k$
-- statement:
--   For an integer $p\ge2$, the tail of the power series of $\ell$:
--   $$r_p(x)=\sum_{k=p}^\infty\frac{x^{2k}}{k},\qquad |x|<1.$$
--   It is negligible on the bulk of the spectrum and blows up near $\pm1$.
--
--   **Formalization Note** It is read on $(-1,1)$ only, where the series converges.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8

import Mathlib

namespace MatrixSpencer

/-- **The tail `r_p(x) = ∑_{k ≥ p} x^{2k}/k`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8.

**Formalization Note.** The series is written as `∑_{k ≥ 0} x^{2(k+p)}/(k+p)`. It converges for
`|x| < 1` and is read there only (for `p ≥ 2`, as on the page). The value at `|x| ≥ 1` is Lean's
junk `tsum` and is never used. -/
noncomputable def tailR (p : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * (k + p)) / ((k : ℝ) + p)

end MatrixSpencer


