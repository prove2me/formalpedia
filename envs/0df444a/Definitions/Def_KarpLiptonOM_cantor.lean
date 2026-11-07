-- Prove2me | Definitions.Def_KarpLiptonOM_cantor
-- name    : KarpLiptonOM_cantor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:47.31919+00:00
-- url     : https://prove2.me/theorems/0d00ac5b-cad6-460f-9029-1b297efe3506
-- title:
--   Cantor pairing $\pi(n, i) = \binom{n+i+1}{2} + i$
-- statement:
--   The **Cantor pairing** is
--   $$
--   \pi(n, i) = \binom{n+i+1}{2} + i ,
--   $$
--   a bijection $\mathbb N^2 \to \mathbb N$ with $\pi(n, i) \le (n+i+1)^2$, computable and invertible in time polynomial in the unary lengths. Tally languages $\{1^{\pi(n,i)} : \dots\}$ store bit $i$ of an advice string for length $n$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib

namespace KarpLiptonOM

/-- The Cantor pairing `π(n, i) = C(n+i+1, 2) + i` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20), a bijection `ℕ² → ℕ`. -/
def cantor (n i : ℕ) : ℕ := (n + i + 1).choose 2 + i

end KarpLiptonOM


