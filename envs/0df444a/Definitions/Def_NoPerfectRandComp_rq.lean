-- Prove2me | Definitions.Def_NoPerfectRandComp_rq
-- name    : NoPerfectRandComp_rq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:07.521498+00:00
-- url     : https://prove2.me/theorems/99eddfa4-492c-4ad7-9247-489846ec9e68
-- title:
--   Hamming radius $r_q = 5000q^4 - 500q^3$
-- statement:
--   The radius of the Hamming ball of the approximate-index seed is
--   $$
--   r_q = 5000\,q^4 - 500\,q^3 .
--   $$
--
--   **Formalization Note** Natural-number subtraction; it is exact because $500q^3 \le 5000q^4$ for every $q$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (10), p.12, and Eq. (16), p.17

import Mathlib

namespace NoPerfectRandComp

/-- The Hamming radius `r_q = 5000 q⁴ − 500 q³` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (10), p.12 and (16), p.17).
The natural-number subtraction is exact (`500 q³ ≤ 5000 q⁴` for every `q`). -/
def rq (q : ℕ) : ℕ := 5000 * q ^ 4 - 500 * q ^ 3

end NoPerfectRandComp


