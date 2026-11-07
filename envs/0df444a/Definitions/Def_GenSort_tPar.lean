-- Prove2me | Definitions.Def_GenSort_tPar
-- name    : GenSort_tPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:13.621508+00:00
-- url     : https://prove2.me/theorems/b4ad5fa5-362d-4204-a78d-b5fbed323135
-- title:
--   Selection size $t = d/(2^{12}\log n)$
-- statement:
--   In each pass, every right vertex selects its
--   $$
--   t = \Big\lceil \frac{d}{2^{12} \log n} \Big\rceil
--   $$
--   highest-score left neighbours.
--
--   **Formalization Note** Rounded up to a positive integer; $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.9 (PDF p.11)

import Mathlib

namespace GenSort

/-- **The protocol parameter `t := d / (2^12 log n)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.9 (PDF p.11): the number of
highest-score left neighbours selected at each right vertex.

**Formalization Note.** Rounded up to an integer; `log` is `log₂`. -/
noncomputable def tPar (n d : ℕ) : ℕ := ⌈(d : ℝ) / (2 ^ 12 * Real.logb 2 n)⌉₊

end GenSort


