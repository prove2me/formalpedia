-- Prove2me | Definitions.Def_NoPerfectRandComp_bq
-- name    : NoPerfectRandComp_bq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:09.272815+00:00
-- url     : https://prove2.me/theorems/75f55556-6983-4c48-a39a-8c4307d2c90f
-- title:
--   Pointer payload length $b_q = 1 + q(q+1)$
-- statement:
--   The payload length of an encoded pointer cell is
--   $$
--   b_q = 1 + q(q+1),
--   $$
--   enough for the pointer alphabet, since $|A_q| = 2(q+1)^{q+1} \le 2^{b_q}$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Eq. (19), p.18, and p.19

import Mathlib

namespace NoPerfectRandComp

/-- The payload length `b_q = 1 + q(q + 1)` of a pointer cell (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (19), p.18). -/
def bq (q : ℕ) : ℕ := 1 + q * (q + 1)

end NoPerfectRandComp


