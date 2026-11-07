-- Prove2me | Definitions.Def_GenSort_k0
-- name    : GenSort_k0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:00.687864+00:00
-- url     : https://prove2.me/theorems/980e9d5f-db4c-4664-9555-8b97ffe1d2e8
-- title:
--   Coarse and flagging sample size $2^{32} n \log^3 n$
-- statement:
--   The coarse predictor of §3.1 and the flagging step of §3.3 each sample
--   $$
--   k_0 = \big\lceil 2^{32}\, n \log^3 n \big\rceil
--   $$
--   edges uniformly at random with replacement.
--
--   **Formalization Note** $\log = \log_2$, and the real number is rounded up to an integer.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1, p.5 (PDF p.7) and §3.3, p.6 (PDF p.8)

import Mathlib

namespace GenSort

/-- **Coarse and flagging sample size** `2^32 n log³ n`, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.1, p.5 (PDF p.7) and §3.3,
p.6 (PDF p.8).

**Formalization Note.** `log` is `log₂` and the real number is rounded up to an integer:
`k0 n = ⌈2^32 · n · (log₂ n)³⌉`. -/
noncomputable def k0 (n : ℕ) : ℕ := ⌈(2 : ℝ) ^ 32 * n * Real.logb 2 n ^ 3⌉₊

end GenSort


