-- Prove2me | Definitions.Def_LinfContractionFP_clipInterval
-- name    : LinfContractionFP_clipInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:54.51029+00:00
-- url     : https://prove2.me/theorems/6b1f917d-df19-450f-9d1c-7628acc573ea
-- title:
--   Clipping a real onto $[a,b]$
-- statement:
--   For reals $a,b,y$, $\mathrm{clip}_{[a,b]}(y)=\max\{a,\min\{b,y\}\}$. When $a\le b$ this is the nearest point of $[a,b]$ to $y$.
--
--   It is used for the clipping onto the unit cube (Section 3) and in line 8 of Algorithm 2.
--
--   **Formalization Note** The minimum with the upper end is taken first, then the maximum with the lower end; for $a>b$ the value is $a$. Algorithm 2 only clips onto nonempty intervals, so the order never matters there.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Section 3, p.5; Algorithm 2, line 8, p.9

import Mathlib

namespace LinfContractionFP

/-- Clipping a real `y` onto the interval `[a, b]`: `clip[a,b](y) = max a (min b y)`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Section 3, p.5
(`clip[0,1]^d`) and Algorithm 2, line 8, p.9 (`clip[U_i − t, L_i + t]`, `clip[L_i + t, U_i − t]`).

**Formalization Note.** The order is: first `min` with the upper end `b`, then `max` with the
lower end `a`. When `a ≤ b` this is the usual projection onto `[a, b]`; when `a > b` it returns
`a`. Algorithm 2 applies it only to nonempty intervals (for a narrow coordinate
`U_i − t < L_i + t`, for a wide one `L_i + t < U_i − t`), so the order never matters there. -/
def clipInterval (a b y : ℝ) : ℝ := max a (min b y)

end LinfContractionFP


