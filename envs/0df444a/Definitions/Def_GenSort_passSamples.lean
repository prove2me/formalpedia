-- Prove2me | Definitions.Def_GenSort_passSamples
-- name    : GenSort_passSamples
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:07.788095+00:00
-- url     : https://prove2.me/theorems/8610322e-534a-43ad-9637-0e804c59e67b
-- title:
--   Sampling budget of a pass $16d\,(s + 2^{10} s\log n)$
-- statement:
--   A pass draws
--   $$
--   M' = 16d\,\big(s + \lceil 2^{10} s \log n\rceil\big)
--   $$
--   uniformly random edges of the current graph and queries them; if fewer than $s + \lceil 2^{10} s \log n\rceil$ of them are bad, the pass terminates prematurely.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 step 1, p.9 (PDF p.11) and Claim 3.6, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_mPar

namespace GenSort

/-- **The sampling budget of a pass, `16d · (s + 2^10 s log n)`**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 step 1, p.9 (PDF
p.11) and Claim 3.6, p.10, with `s = sPar n d` and `2^10 s log n` rounded up (`mPar n d`). -/
noncomputable def passSamples (n d : ℕ) : ℕ := 16 * d * (sPar n d + mPar n d)

end GenSort


