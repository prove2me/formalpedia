-- Prove2me | Definitions.Def_GenSort_mPar
-- name    : GenSort_mPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:41.437374+00:00
-- url     : https://prove2.me/theorems/fc692846-fdd3-4eee-b824-653aee916d1f
-- title:
--   Number of validation edges $2^{10} s \log n$
-- statement:
--   After the $s$ training edges, a pass uses the next $\lceil 2^{10} s \log n \rceil$ bad sampled edges as validation edges, with $s$ the §3.5 parameter.
--
--   **Formalization Note** Rounded up; $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 step 1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_GenSort_sPar

namespace GenSort

/-- **The number of validation edges `2^10 s log n`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 step 1, p.9 (PDF p.11), for the
`s` of §3.5.

**Formalization Note.** Rounded up to an integer; `log` is `log₂`. -/
noncomputable def mPar (n d : ℕ) : ℕ := ⌈(2 : ℝ) ^ 10 * sPar n d * Real.logb 2 n⌉₊

end GenSort


