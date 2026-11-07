-- Prove2me | Definitions.Def_GenSort_sPar
-- name    : GenSort_sPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:05.68877+00:00
-- url     : https://prove2.me/theorems/b23a8d0c-2d17-4651-9bb5-7918ecf2d85b
-- title:
--   Number of training edges $s = 2^{18} n\log n / d$
-- statement:
--   The error isolation protocol is run with
--   $$
--   s = \Big\lceil \frac{2^{18}\, n \log n}{d} \Big\rceil
--   $$
--   training edges in each pass.
--
--   **Formalization Note** §3.4 asks for a positive integer and the displayed value is a fraction, so it is rounded up; $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.9 (PDF p.11)

import Mathlib

namespace GenSort

/-- **The protocol parameter `s := 2^18 · n log n / d`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.9 (PDF p.11): the number
of training edges of a pass.

**Formalization Note.** §3.4 asks for positive integers; the displayed value is rounded up, and
`log` is `log₂`: `sPar n d = ⌈2^18 · n · log₂ n / d⌉`. -/
noncomputable def sPar (n d : ℕ) : ℕ := ⌈(2 : ℝ) ^ 18 * n * Real.logb 2 n / d⌉₊

end GenSort


