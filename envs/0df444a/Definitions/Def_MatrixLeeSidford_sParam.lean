-- Prove2me | Definitions.Def_MatrixLeeSidford_sParam
-- name    : MatrixLeeSidford_sParam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:15.785062+00:00
-- url     : https://prove2.me/theorems/89bcbe6b-a1dd-49f5-8269-dabcacc20f06
-- title:
--   Trace-power exponent $s=2\lceil\log(2mn)\rceil$
-- statement:
--   The trace-power exponent of the barrier is
--   $$
--   s=2\lceil\log(2mn)\rceil ,
--   $$
--   with the natural logarithm. For $m,n\ge1$ it is an even integer $\ge2$, and $p=2s$.
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29

import Mathlib

namespace MatrixLeeSidford

/-- The trace-power exponent `s := 2⌈log(2mn)⌉` (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), Definition 5.1, p.37; Theorem 2.1, p.29).

**Formalization Note** Natural logarithm `Real.log` and the natural-number ceiling `⌈·⌉₊`;
`s : ℕ`. For `m, n ≥ 1`, `log(2mn) ≥ log 2 > 0`, so `s ≥ 2`. -/
noncomputable def sParam (m n : ℕ) : ℕ :=
  2 * ⌈Real.log (2 * (m : ℝ) * n)⌉₊

end MatrixLeeSidford


