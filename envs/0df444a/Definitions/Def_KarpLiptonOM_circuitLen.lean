-- Prove2me | Definitions.Def_KarpLiptonOM_circuitLen
-- name    : KarpLiptonOM_circuitLen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:26.013034+00:00
-- url     : https://prove2.me/theorems/e6c7be8a-72d6-410c-9938-e9cdb3dca76e
-- title:
--   Length $\ell(n, s)$ of the circuit encoding
-- statement:
--   Circuits with $n$ inputs and at most $s$ gates are encoded by strings of length exactly
--   $$
--   \ell(n, s) = s\,\bigl(3 + 2\,b\bigr), \qquad b = \text{number of binary digits of } n + s ,
--   $$
--   which is $O(s \log(n + s))$, as the paper requires.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib

namespace KarpLiptonOM

/-- The length `ℓ(n, s) = s · (3 + 2⌈log₂(n + s + 1)⌉)` of the fixed encoding of circuits with `n`
inputs and at most `s` gates (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20: "strings of length exactly
`ℓ(n, s) = O(s log(n + s))`").

**Formalization Note** `Nat.size (n + s)` is the number of binary digits of `n + s`, which suffices
for every wire index `< n + s`. -/
def circuitLen (n s : ℕ) : ℕ := s * (3 + 2 * Nat.size (n + s))

end KarpLiptonOM


